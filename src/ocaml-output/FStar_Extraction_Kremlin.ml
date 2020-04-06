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
  fun projectee  -> match projectee with | { name; typ = typ1; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ = typ1; mut;_} -> typ1 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ = typ1; mut;_} -> mut 
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
  'uuuuuu4324 'uuuuuu4325 'uuuuuu4326 .
    ('uuuuuu4324 * 'uuuuuu4325 * 'uuuuuu4326) -> 'uuuuuu4324
  = fun uu____4337  -> match uu____4337 with | (x,uu____4345,uu____4346) -> x 
let snd3 :
  'uuuuuu4356 'uuuuuu4357 'uuuuuu4358 .
    ('uuuuuu4356 * 'uuuuuu4357 * 'uuuuuu4358) -> 'uuuuuu4357
  = fun uu____4369  -> match uu____4369 with | (uu____4376,x,uu____4378) -> x 
let thd3 :
  'uuuuuu4388 'uuuuuu4389 'uuuuuu4390 .
    ('uuuuuu4388 * 'uuuuuu4389 * 'uuuuuu4390) -> 'uuuuuu4390
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
  fun op1  -> (mk_bool_op op1) <> FStar_Pervasives_Native.None 
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
  fun op1  -> (mk_op op1) <> FStar_Pervasives_Native.None 
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
  fun projectee  -> match projectee with | { pretty;_} -> pretty 
let (empty : Prims.string Prims.list -> env) =
  fun module_name  -> { names = []; names_t = []; module_name } 
let (extend : env -> Prims.string -> env) =
  fun env1  ->
    fun x  ->
      let uu___168_4672 = env1  in
      {
        names = ({ pretty = x } :: (env1.names));
        names_t = (uu___168_4672.names_t);
        module_name = (uu___168_4672.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env1  ->
    fun x  ->
      let uu___172_4686 = env1  in
      {
        names = (uu___172_4686.names);
        names_t = (x :: (env1.names_t));
        module_name = (uu___172_4686.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env1  ->
    fun x  ->
      let uu____4701 =
        FStar_List.tryFind (fun name1  -> name1.pretty = x) env1.names  in
      match uu____4701 with
      | FStar_Pervasives_Native.Some name1 -> name1
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env1  ->
    fun x  ->
      try
        (fun uu___183_4725  ->
           match () with
           | () ->
               FStar_List.index (fun name1  -> name1.pretty = x) env1.names)
          ()
      with
      | uu___182_4732 ->
          let uu____4734 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4734
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env1  ->
    fun x  ->
      try
        (fun uu___192_4754  ->
           match () with
           | () -> FStar_List.index (fun name1  -> name1 = x) env1.names_t)
          ()
      with
      | uu___191_4763 ->
          let uu____4765 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4765
  
let add_binders :
  'uuuuuu4776 . env -> (Prims.string * 'uuuuuu4776) Prims.list -> env =
  fun env1  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____4811  ->
             match uu____4811 with | (name1,uu____4818) -> extend env2 name1)
        env1 binders
  
let (list_elements :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list)
  =
  fun e2  ->
    let rec list_elements acc e21 =
      match e21.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Cons"),hd::tl::[])
          -> list_elements (hd :: acc) tl
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
        let program1 =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5146 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program1)

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
  fun env1  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env1 flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5218 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env1) tys
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
  fun env1  ->
    fun flavor  ->
      fun lb  ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
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
            let name2 = ((env1.module_name), name1)  in
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
                  let uu____5349 = translate_type env1 t0  in
                  (uu____5343, uu____5346, name2, uu____5349, arg_names)  in
                DExternal uu____5317  in
              FStar_Pervasives_Native.Some uu____5316
            else
              ((let uu____5368 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name2  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5368);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
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
              (let env2 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env1 name1
                 else env1  in
               let env3 =
                 FStar_List.fold_left
                   (fun env3  -> fun name2  -> extend_t env3 name2) env2
                   tvars
                  in
               let rec find_return_type eff i uu___6_5437 =
                 match uu___6_5437 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5446,eff1,t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t)  in
               let name2 = ((env3.module_name), name1)  in
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
                         FStar_Extraction_ML_Syntax.string_of_mlpath name2
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5492 msg)
                    else ();
                    (let t1 = translate_type env3 t  in
                     let binders = translate_binders env3 args  in
                     let env4 = add_binders env3 args  in
                     let cc1 = translate_cc meta  in
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
                              let body1 = translate_expr env4 body  in
                              FStar_Pervasives_Native.Some
                                (DFunction
                                   (cc1, meta1, (FStar_List.length tvars),
                                     t1, name2, binders, body1))) ()
                     with
                     | e ->
                         let msg = FStar_Util.print_exn e  in
                         ((let uu____5558 =
                             let uu____5564 =
                               let uu____5566 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name2
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
                                (cc1, meta1, (FStar_List.length tvars), t1,
                                  name2, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5592;
            FStar_Extraction_ML_Syntax.mllb_def = expr1;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5595;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = translate_flags meta  in
               let env2 =
                 FStar_List.fold_left
                   (fun env2  -> fun name2  -> extend_t env2 name2) env1
                   tvars
                  in
               let t1 = translate_type env2 t  in
               let name2 = ((env2.module_name), name1)  in
               try
                 (fun uu___393_5632  ->
                    match () with
                    | () ->
                        let expr2 = translate_expr env2 expr1  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name2, (FStar_List.length tvars), t1,
                               expr2))) ()
               with
               | e ->
                   ((let uu____5656 =
                       let uu____5662 =
                         let uu____5664 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name2
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
                         (meta1, name2, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5684;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5685;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5686;
            FStar_Extraction_ML_Syntax.print_typ = uu____5687;_} ->
            ((let uu____5694 =
                let uu____5700 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name1
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
  fun env1  ->
    fun ty  ->
      let uu____5721 = ty  in
      match uu____5721 with
      | (uu____5724,uu____5725,uu____5726,uu____5727,flags,uu____5729) ->
          if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags
          then FStar_Pervasives_Native.None
          else
            (match ty with
             | (assumed,name1,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
                 let name2 = ((env1.module_name), name1)  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  -> fun name3  -> extend_t env2 name3) env1
                     args
                    in
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
                        FStar_Extraction_ML_Syntax.string_of_mlpath name2  in
                      FStar_Util.print1_warning
                        "Not extracting type definition %s to KreMLin (assumed type)\n"
                        name3;
                      FStar_Pervasives_Native.None)
                   else
                     (let uu____5803 =
                        let uu____5804 =
                          let uu____5824 = translate_flags flags1  in
                          let uu____5827 = translate_type env2 t  in
                          (name2, uu____5824, (FStar_List.length args),
                            uu____5827)
                           in
                        DTypeAlias uu____5804  in
                      FStar_Pervasives_Native.Some uu____5803)
             | (uu____5840,name1,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name2 = ((env1.module_name), name1)  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  -> fun name3  -> extend_t env2 name3) env1
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
                                  let uu____5979 = translate_type env2 t  in
                                  (uu____5979, false)  in
                                (f, uu____5973)) fields
                        in
                     (name2, uu____5918, (FStar_List.length args),
                       uu____5921)
                      in
                   DTypeFlat uu____5886  in
                 FStar_Pervasives_Native.Some uu____5885
             | (uu____6012,name1,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches1)) ->
                 let name2 = ((env1.module_name), name1)  in
                 let flags2 = translate_flags flags1  in
                 let env2 = FStar_List.fold_left extend_t env1 args  in
                 let uu____6062 =
                   let uu____6063 =
                     let uu____6102 =
                       FStar_List.map
                         (fun uu____6155  ->
                            match uu____6155 with
                            | (cons,ts) ->
                                let uu____6203 =
                                  FStar_List.map
                                    (fun uu____6235  ->
                                       match uu____6235 with
                                       | (name3,t) ->
                                           let uu____6255 =
                                             let uu____6261 =
                                               translate_type env2 t  in
                                             (uu____6261, false)  in
                                           (name3, uu____6255)) ts
                                   in
                                (cons, uu____6203)) branches1
                        in
                     (name2, flags2, (FStar_List.length args), uu____6102)
                      in
                   DTypeVariant uu____6063  in
                 FStar_Pervasives_Native.Some uu____6062
             | (uu____6314,name1,_mangled_name,uu____6317,uu____6318,uu____6319)
                 ->
                 ((let uu____6335 =
                     let uu____6341 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name1
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6341)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6335);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name1 ->
          let uu____6349 = find_t env1 name1  in TBound uu____6349
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6352,t2) ->
          let uu____6354 =
            let uu____6359 = translate_type env1 t1  in
            let uu____6360 = translate_type env1 t2  in
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
          -> let uu____6438 = translate_type env1 arg  in TBuf uu____6438
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
          -> let uu____6500 = translate_type env1 arg  in TBuf uu____6500
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6502::uu____6503::[],p) when
          let uu____6507 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6507 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6511 = translate_type env1 arg  in TBuf uu____6511
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6516 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6516 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6520 = translate_type env1 arg  in TConstBuf uu____6520
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
          -> let uu____6596 = translate_type env1 arg  in TBuf uu____6596
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6597::arg::[],p) when
          (let uu____6604 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6604 = "FStar.HyperStack.s_ref") ||
            (let uu____6609 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6609 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6613 = translate_type env1 arg  in TBuf uu____6613
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6614::[],p) when
          let uu____6618 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6618 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6670 = FStar_List.map (translate_type env1) args  in
          TTuple uu____6670
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6681 =
              let uu____6696 = FStar_List.map (translate_type env1) args  in
              (lid, uu____6696)  in
            TApp uu____6681
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6714 = FStar_List.map (translate_type env1) ts  in
          TTuple uu____6714

and (translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
      Prims.list -> binder Prims.list)
  = fun env1  -> fun args  -> FStar_List.map (translate_binder env1) args

and (translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) ->
      binder)
  =
  fun env1  ->
    fun uu____6732  ->
      match uu____6732 with
      | (name1,typ1) ->
          let uu____6742 = translate_type env1 typ1  in
          { name = name1; typ = uu____6742; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env1  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name1 ->
          let uu____6749 = find env1 name1  in EBound uu____6749
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op1) when
          (is_machine_int m) && (is_op op1) ->
          let uu____6763 =
            let uu____6768 = FStar_Util.must (mk_op op1)  in
            let uu____6769 = FStar_Util.must (mk_width m)  in
            (uu____6768, uu____6769)  in
          EOp uu____6763
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op1) when
          is_bool_op op1 ->
          let uu____6779 =
            let uu____6784 = FStar_Util.must (mk_bool_op op1)  in
            (uu____6784, Bool)  in
          EOp uu____6779
      | FStar_Extraction_ML_Syntax.MLE_Name n -> EQualified n
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,{ FStar_Extraction_ML_Syntax.mllb_name = name1;
                     FStar_Extraction_ML_Syntax.mllb_tysc =
                       FStar_Pervasives_Native.Some ([],typ1);
                     FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
                     FStar_Extraction_ML_Syntax.mllb_def = body;
                     FStar_Extraction_ML_Syntax.mllb_meta = flags;
                     FStar_Extraction_ML_Syntax.print_typ = print;_}::[]),continuation)
          ->
          let binder1 =
            let uu____6807 = translate_type env1 typ1  in
            { name = name1; typ = uu____6807; mut = false }  in
          let body1 = translate_expr env1 body  in
          let env2 = extend env1 name1  in
          let continuation1 = translate_expr env2 continuation  in
          ELet (binder1, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr1,branches1) ->
          let uu____6834 =
            let uu____6845 = translate_expr env1 expr1  in
            let uu____6846 = translate_branches env1 branches1  in
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
            let uu____6879 = translate_expr env1 arg  in
            let uu____6880 = translate_type env1 t  in
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
            let uu____6924 = translate_type env1 t  in (s, uu____6924)  in
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
               let print_nm = (["FStar"; "HyperStack"; "IO"], "print_string")
                  in
               let print =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_Name print_nm)
                  in
               let print1 =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_App (print, [arg]))
                  in
               let t = translate_expr env1 print1  in ESequence [t; EAbort])
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
             FStar_Extraction_ML_Syntax.loc = uu____6991;_},e1::[])
          when
          (let uu____7001 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7001 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____7006 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7006 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7011;
                  FStar_Extraction_ML_Syntax.loc = uu____7012;_},uu____7013);
             FStar_Extraction_ML_Syntax.mlty = uu____7014;
             FStar_Extraction_ML_Syntax.loc = uu____7015;_},e1::e2::[])
          when
          ((((let uu____7026 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7026 = "FStar.Buffer.index") ||
               (let uu____7031 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7031 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____7036 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7036 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____7041 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7041 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____7046 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7046 = "LowStar.ConstBuffer.index")
          ->
          let uu____7050 =
            let uu____7055 = translate_expr env1 e1  in
            let uu____7056 = translate_expr env1 e2  in
            (uu____7055, uu____7056)  in
          EBufRead uu____7050
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7058;
                  FStar_Extraction_ML_Syntax.loc = uu____7059;_},uu____7060);
             FStar_Extraction_ML_Syntax.mlty = uu____7061;
             FStar_Extraction_ML_Syntax.loc = uu____7062;_},e1::[])
          when
          let uu____7070 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7070 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____7074 =
            let uu____7079 = translate_expr env1 e1  in
            (uu____7079, (EConstant (UInt32, "0")))  in
          EBufRead uu____7074
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7083;
                  FStar_Extraction_ML_Syntax.loc = uu____7084;_},uu____7085);
             FStar_Extraction_ML_Syntax.mlty = uu____7086;
             FStar_Extraction_ML_Syntax.loc = uu____7087;_},e1::e2::[])
          when
          ((let uu____7098 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7098 = "FStar.Buffer.create") ||
             (let uu____7103 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7103 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7108 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7108 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7112 =
            let uu____7119 = translate_expr env1 e1  in
            let uu____7120 = translate_expr env1 e2  in
            (Stack, uu____7119, uu____7120)  in
          EBufCreate uu____7112
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7122;
                  FStar_Extraction_ML_Syntax.loc = uu____7123;_},uu____7124);
             FStar_Extraction_ML_Syntax.mlty = uu____7125;
             FStar_Extraction_ML_Syntax.loc = uu____7126;_},elen::[])
          when
          let uu____7134 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7134 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7138 =
            let uu____7143 = translate_expr env1 elen  in (Stack, uu____7143)
             in
          EBufCreateNoInit uu____7138
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7145;
                  FStar_Extraction_ML_Syntax.loc = uu____7146;_},uu____7147);
             FStar_Extraction_ML_Syntax.mlty = uu____7148;
             FStar_Extraction_ML_Syntax.loc = uu____7149;_},init::[])
          when
          let uu____7157 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7157 = "FStar.HyperStack.ST.salloc" ->
          let uu____7161 =
            let uu____7168 = translate_expr env1 init  in
            (Stack, uu____7168, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7161
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7172;
                  FStar_Extraction_ML_Syntax.loc = uu____7173;_},uu____7174);
             FStar_Extraction_ML_Syntax.mlty = uu____7175;
             FStar_Extraction_ML_Syntax.loc = uu____7176;_},e2::[])
          when
          ((let uu____7186 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7186 = "FStar.Buffer.createL") ||
             (let uu____7191 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7191 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7196 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7196 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7200 =
            let uu____7207 =
              let uu____7210 = list_elements e2  in
              FStar_List.map (translate_expr env1) uu____7210  in
            (Stack, uu____7207)  in
          EBufCreateL uu____7200
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7216;
                  FStar_Extraction_ML_Syntax.loc = uu____7217;_},uu____7218);
             FStar_Extraction_ML_Syntax.mlty = uu____7219;
             FStar_Extraction_ML_Syntax.loc = uu____7220;_},_erid::e2::[])
          when
          (let uu____7231 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7231 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7236 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7236 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7240 =
            let uu____7247 =
              let uu____7250 = list_elements e2  in
              FStar_List.map (translate_expr env1) uu____7250  in
            (Eternal, uu____7247)  in
          EBufCreateL uu____7240
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7256;
                  FStar_Extraction_ML_Syntax.loc = uu____7257;_},uu____7258);
             FStar_Extraction_ML_Syntax.mlty = uu____7259;
             FStar_Extraction_ML_Syntax.loc = uu____7260;_},_rid::init::[])
          when
          (let uu____7271 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7271 = "FStar.HyperStack.ST.ralloc") ||
            (let uu____7276 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7276 = "FStar.HyperStack.ST.ralloc_drgn")
          ->
          let uu____7280 =
            let uu____7287 = translate_expr env1 init  in
            (Eternal, uu____7287, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7280
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7291;
                  FStar_Extraction_ML_Syntax.loc = uu____7292;_},uu____7293);
             FStar_Extraction_ML_Syntax.mlty = uu____7294;
             FStar_Extraction_ML_Syntax.loc = uu____7295;_},_e0::e1::e2::[])
          when
          ((let uu____7307 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7307 = "FStar.Buffer.rcreate") ||
             (let uu____7312 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7312 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7317 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7317 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7321 =
            let uu____7328 = translate_expr env1 e1  in
            let uu____7329 = translate_expr env1 e2  in
            (Eternal, uu____7328, uu____7329)  in
          EBufCreate uu____7321
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7331;
                  FStar_Extraction_ML_Syntax.loc = uu____7332;_},uu____7333);
             FStar_Extraction_ML_Syntax.mlty = uu____7334;
             FStar_Extraction_ML_Syntax.loc = uu____7335;_},uu____7336)
          when
          (((((let uu____7347 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7347 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7352 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____7352 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7357 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7357 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7362 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7362 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7367 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7367 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7372 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7372 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7378;
                  FStar_Extraction_ML_Syntax.loc = uu____7379;_},uu____7380);
             FStar_Extraction_ML_Syntax.mlty = uu____7381;
             FStar_Extraction_ML_Syntax.loc = uu____7382;_},_erid::elen::[])
          when
          let uu____7391 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7391 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7395 =
            let uu____7400 = translate_expr env1 elen  in
            (Eternal, uu____7400)  in
          EBufCreateNoInit uu____7395
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7402;
                  FStar_Extraction_ML_Syntax.loc = uu____7403;_},uu____7404);
             FStar_Extraction_ML_Syntax.mlty = uu____7405;
             FStar_Extraction_ML_Syntax.loc = uu____7406;_},_rid::init::[])
          when
          (let uu____7417 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7417 = "FStar.HyperStack.ST.ralloc_mm") ||
            (let uu____7422 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7422 = "FStar.HyperStack.ST.ralloc_drgn_mm")
          ->
          let uu____7426 =
            let uu____7433 = translate_expr env1 init  in
            (ManuallyManaged, uu____7433, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7426
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7437;
                  FStar_Extraction_ML_Syntax.loc = uu____7438;_},uu____7439);
             FStar_Extraction_ML_Syntax.mlty = uu____7440;
             FStar_Extraction_ML_Syntax.loc = uu____7441;_},_e0::e1::e2::[])
          when
          (((let uu____7453 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7453 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7458 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7458 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7463 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7463 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7468 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7468 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7472 =
            let uu____7479 = translate_expr env1 e1  in
            let uu____7480 = translate_expr env1 e2  in
            (ManuallyManaged, uu____7479, uu____7480)  in
          EBufCreate uu____7472
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
             FStar_Extraction_ML_Syntax.loc = uu____7486;_},_erid::elen::[])
          when
          let uu____7495 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7495 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7499 =
            let uu____7504 = translate_expr env1 elen  in
            (ManuallyManaged, uu____7504)  in
          EBufCreateNoInit uu____7499
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7506;
                  FStar_Extraction_ML_Syntax.loc = uu____7507;_},uu____7508);
             FStar_Extraction_ML_Syntax.mlty = uu____7509;
             FStar_Extraction_ML_Syntax.loc = uu____7510;_},e2::[])
          when
          let uu____7518 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7518 = "FStar.HyperStack.ST.rfree" ->
          let uu____7522 = translate_expr env1 e2  in EBufFree uu____7522
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
             FStar_Extraction_ML_Syntax.loc = uu____7528;_},e2::[])
          when
          (let uu____7538 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7538 = "FStar.Buffer.rfree") ||
            (let uu____7543 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7543 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7547 = translate_expr env1 e2  in EBufFree uu____7547
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7549;
                  FStar_Extraction_ML_Syntax.loc = uu____7550;_},uu____7551);
             FStar_Extraction_ML_Syntax.mlty = uu____7552;
             FStar_Extraction_ML_Syntax.loc = uu____7553;_},e1::e2::_e3::[])
          when
          let uu____7563 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7563 = "FStar.Buffer.sub" ->
          let uu____7567 =
            let uu____7572 = translate_expr env1 e1  in
            let uu____7573 = translate_expr env1 e2  in
            (uu____7572, uu____7573)  in
          EBufSub uu____7567
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7575;
                  FStar_Extraction_ML_Syntax.loc = uu____7576;_},uu____7577);
             FStar_Extraction_ML_Syntax.mlty = uu____7578;
             FStar_Extraction_ML_Syntax.loc = uu____7579;_},e1::e2::_e3::[])
          when
          (let uu____7591 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7591 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7596 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7596 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7600 =
            let uu____7605 = translate_expr env1 e1  in
            let uu____7606 = translate_expr env1 e2  in
            (uu____7605, uu____7606)  in
          EBufSub uu____7600
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7608;
                  FStar_Extraction_ML_Syntax.loc = uu____7609;_},uu____7610);
             FStar_Extraction_ML_Syntax.mlty = uu____7611;
             FStar_Extraction_ML_Syntax.loc = uu____7612;_},e1::e2::[])
          when
          let uu____7621 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7621 = "FStar.Buffer.join" -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7626;
                  FStar_Extraction_ML_Syntax.loc = uu____7627;_},uu____7628);
             FStar_Extraction_ML_Syntax.mlty = uu____7629;
             FStar_Extraction_ML_Syntax.loc = uu____7630;_},e1::e2::[])
          when
          let uu____7639 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7639 = "FStar.Buffer.offset" ->
          let uu____7643 =
            let uu____7648 = translate_expr env1 e1  in
            let uu____7649 = translate_expr env1 e2  in
            (uu____7648, uu____7649)  in
          EBufSub uu____7643
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7651;
                  FStar_Extraction_ML_Syntax.loc = uu____7652;_},uu____7653);
             FStar_Extraction_ML_Syntax.mlty = uu____7654;
             FStar_Extraction_ML_Syntax.loc = uu____7655;_},e1::e2::[])
          when
          let uu____7664 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7664 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7668 =
            let uu____7673 = translate_expr env1 e1  in
            let uu____7674 = translate_expr env1 e2  in
            (uu____7673, uu____7674)  in
          EBufSub uu____7668
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
             FStar_Extraction_ML_Syntax.loc = uu____7680;_},e1::e2::e3::[])
          when
          (((let uu____7692 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7692 = "FStar.Buffer.upd") ||
              (let uu____7697 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7697 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7702 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7702 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7707 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7707 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7711 =
            let uu____7718 = translate_expr env1 e1  in
            let uu____7719 = translate_expr env1 e2  in
            let uu____7720 = translate_expr env1 e3  in
            (uu____7718, uu____7719, uu____7720)  in
          EBufWrite uu____7711
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7722;
                  FStar_Extraction_ML_Syntax.loc = uu____7723;_},uu____7724);
             FStar_Extraction_ML_Syntax.mlty = uu____7725;
             FStar_Extraction_ML_Syntax.loc = uu____7726;_},e1::e2::[])
          when
          let uu____7735 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7735 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7739 =
            let uu____7746 = translate_expr env1 e1  in
            let uu____7747 = translate_expr env1 e2  in
            (uu____7746, (EConstant (UInt32, "0")), uu____7747)  in
          EBufWrite uu____7739
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7751;
             FStar_Extraction_ML_Syntax.loc = uu____7752;_},uu____7753::[])
          when
          let uu____7756 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7756 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7761;
             FStar_Extraction_ML_Syntax.loc = uu____7762;_},uu____7763::[])
          when
          let uu____7766 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7766 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7771;
                  FStar_Extraction_ML_Syntax.loc = uu____7772;_},uu____7773);
             FStar_Extraction_ML_Syntax.mlty = uu____7774;
             FStar_Extraction_ML_Syntax.loc = uu____7775;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7789 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7789 = "FStar.Buffer.blit") ||
             (let uu____7794 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7794 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7799 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7799 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7803 =
            let uu____7814 = translate_expr env1 e1  in
            let uu____7815 = translate_expr env1 e2  in
            let uu____7816 = translate_expr env1 e3  in
            let uu____7817 = translate_expr env1 e4  in
            let uu____7818 = translate_expr env1 e5  in
            (uu____7814, uu____7815, uu____7816, uu____7817, uu____7818)  in
          EBufBlit uu____7803
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7820;
                  FStar_Extraction_ML_Syntax.loc = uu____7821;_},uu____7822);
             FStar_Extraction_ML_Syntax.mlty = uu____7823;
             FStar_Extraction_ML_Syntax.loc = uu____7824;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7840 =
            let uu____7847 = translate_expr env1 e1  in
            let uu____7848 = translate_expr env1 e2  in
            let uu____7849 = translate_expr env1 e3  in
            (uu____7847, uu____7848, uu____7849)  in
          EBufFill uu____7840
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7851;
             FStar_Extraction_ML_Syntax.loc = uu____7852;_},uu____7853::[])
          when
          let uu____7856 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7856 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7861;
                  FStar_Extraction_ML_Syntax.loc = uu____7862;_},uu____7863);
             FStar_Extraction_ML_Syntax.mlty = uu____7864;
             FStar_Extraction_ML_Syntax.loc = uu____7865;_},_rid::[])
          when
          (let uu____7875 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7875 = "FStar.HyperStack.ST.free_drgn") ||
            (let uu____7880 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7880 = "FStar.HyperStack.ST.new_drgn")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7885;
                  FStar_Extraction_ML_Syntax.loc = uu____7886;_},uu____7887);
             FStar_Extraction_ML_Syntax.mlty = uu____7888;
             FStar_Extraction_ML_Syntax.loc = uu____7889;_},_ebuf::_eseq::[])
          when
          (((let uu____7900 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7900 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7905 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7905 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7910 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7910 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7915 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7915 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7920;
                  FStar_Extraction_ML_Syntax.loc = uu____7921;_},uu____7922);
             FStar_Extraction_ML_Syntax.mlty = uu____7923;
             FStar_Extraction_ML_Syntax.loc = uu____7924;_},e1::[])
          when
          (let uu____7934 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7934 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu____7939 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7939 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7944;
                  FStar_Extraction_ML_Syntax.loc = uu____7945;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7947;
             FStar_Extraction_ML_Syntax.loc = uu____7948;_},_eqal::e1::[])
          when
          let uu____7955 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7955 = "LowStar.ConstBuffer.of_qbuf" ->
          let uu____7959 =
            let uu____7964 = translate_expr env1 e1  in
            let uu____7965 =
              let uu____7966 = translate_type env1 t  in TConstBuf uu____7966
               in
            (uu____7964, uu____7965)  in
          ECast uu____7959
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7968;
                  FStar_Extraction_ML_Syntax.loc = uu____7969;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7971;
             FStar_Extraction_ML_Syntax.loc = uu____7972;_},e1::[])
          when
          ((let uu____7980 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7980 = "LowStar.ConstBuffer.cast") ||
             (let uu____7985 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7985 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7990 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7990 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu____7994 =
            let uu____7999 = translate_expr env1 e1  in
            let uu____8000 =
              let uu____8001 = translate_type env1 t  in TBuf uu____8001  in
            (uu____7999, uu____8000)  in
          ECast uu____7994
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____8003;
             FStar_Extraction_ML_Syntax.loc = uu____8004;_},e1::[])
          when
          let uu____8008 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8008 = "Obj.repr" ->
          let uu____8012 =
            let uu____8017 = translate_expr env1 e1  in (uu____8017, TAny)
             in
          ECast uu____8012
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op1);
             FStar_Extraction_ML_Syntax.mlty = uu____8020;
             FStar_Extraction_ML_Syntax.loc = uu____8021;_},args)
          when (is_machine_int m) && (is_op op1) ->
          let uu____8037 = FStar_Util.must (mk_width m)  in
          let uu____8038 = FStar_Util.must (mk_op op1)  in
          mk_op_app env1 uu____8037 uu____8038 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op1);
             FStar_Extraction_ML_Syntax.mlty = uu____8040;
             FStar_Extraction_ML_Syntax.loc = uu____8041;_},args)
          when is_bool_op op1 ->
          let uu____8055 = FStar_Util.must (mk_bool_op op1)  in
          mk_op_app env1 Bool uu____8055 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8057;
             FStar_Extraction_ML_Syntax.loc = uu____8058;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8060;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8061;_}::[])
          when is_machine_int m ->
          let uu____8086 =
            let uu____8092 = FStar_Util.must (mk_width m)  in (uu____8092, c)
             in
          EConstant uu____8086
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8095;
             FStar_Extraction_ML_Syntax.loc = uu____8096;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8098;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8099;_}::[])
          when is_machine_int m ->
          let uu____8124 =
            let uu____8130 = FStar_Util.must (mk_width m)  in (uu____8130, c)
             in
          EConstant uu____8124
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8132;
             FStar_Extraction_ML_Syntax.loc = uu____8133;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8135;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8136;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8149 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8151;
             FStar_Extraction_ML_Syntax.loc = uu____8152;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8154;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8155;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8172 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8174;
             FStar_Extraction_ML_Syntax.loc = uu____8175;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8177;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8178;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8193 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8196;
                  FStar_Extraction_ML_Syntax.loc = uu____8197;_},uu____8198);
             FStar_Extraction_ML_Syntax.mlty = uu____8199;
             FStar_Extraction_ML_Syntax.loc = uu____8200;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = ebefore;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8202;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8203;_}::e1::
           { FStar_Extraction_ML_Syntax.expr = eafter;
             FStar_Extraction_ML_Syntax.mlty = uu____8206;
             FStar_Extraction_ML_Syntax.loc = uu____8207;_}::[])
          when
          let uu____8214 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8214 = "LowStar.Comment.comment_gen" ->
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
                (let uu____8234 =
                   let uu____8243 = translate_expr env1 e1  in
                   (sbefore, uu____8243, safter)  in
                 EComment uu____8234))
           | uu____8246 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____8253;
             FStar_Extraction_ML_Syntax.loc = uu____8254;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8256;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8257;_}::[])
          when
          let uu____8260 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8260 = "LowStar.Comment.comment" ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               (if FStar_Util.contains s "*/"
                then
                  failwith
                    "Standalone Comment contains end-of-comment marker"
                else ();
                EStandaloneComment s)
           | uu____8272 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8274;
             FStar_Extraction_ML_Syntax.loc = uu____8275;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8277;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8278;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8293 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____8296;
             FStar_Extraction_ML_Syntax.loc = uu____8297;_},arg::[])
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
            let uu____8325 =
              let uu____8330 = translate_expr env1 arg  in
              (uu____8330, (TInt UInt64))  in
            ECast uu____8325
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8335 =
                 let uu____8340 = translate_expr env1 arg  in
                 (uu____8340, (TInt UInt32))  in
               ECast uu____8335)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8345 =
                   let uu____8350 = translate_expr env1 arg  in
                   (uu____8350, (TInt UInt16))  in
                 ECast uu____8345)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8355 =
                     let uu____8360 = translate_expr env1 arg  in
                     (uu____8360, (TInt UInt8))  in
                   ECast uu____8355)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8365 =
                       let uu____8370 = translate_expr env1 arg  in
                       (uu____8370, (TInt Int64))  in
                     ECast uu____8365)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8375 =
                         let uu____8380 = translate_expr env1 arg  in
                         (uu____8380, (TInt Int32))  in
                       ECast uu____8375)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8385 =
                           let uu____8390 = translate_expr env1 arg  in
                           (uu____8390, (TInt Int16))  in
                         ECast uu____8385)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8395 =
                             let uu____8400 = translate_expr env1 arg  in
                             (uu____8400, (TInt Int8))  in
                           ECast uu____8395)
                        else
                          (let uu____8403 =
                             let uu____8410 =
                               let uu____8413 = translate_expr env1 arg  in
                               [uu____8413]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8410)
                              in
                           EApp uu____8403)
      | FStar_Extraction_ML_Syntax.MLE_App (head,args) ->
          let uu____8433 =
            let uu____8440 = translate_expr env1 head  in
            let uu____8441 = FStar_List.map (translate_expr env1) args  in
            (uu____8440, uu____8441)  in
          EApp uu____8433
      | FStar_Extraction_ML_Syntax.MLE_TApp (head,ty_args) ->
          let uu____8452 =
            let uu____8459 = translate_expr env1 head  in
            let uu____8460 = FStar_List.map (translate_type env1) ty_args  in
            (uu____8459, uu____8460)  in
          ETypApp uu____8452
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8468 =
            let uu____8473 = translate_expr env1 e1  in
            let uu____8474 = translate_type env1 t_to  in
            (uu____8473, uu____8474)  in
          ECast uu____8468
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8475,fields) ->
          let uu____8497 =
            let uu____8509 =
              assert_lid env1 e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8510 =
              FStar_List.map
                (fun uu____8532  ->
                   match uu____8532 with
                   | (field,expr1) ->
                       let uu____8547 = translate_expr env1 expr1  in
                       (field, uu____8547)) fields
               in
            (uu____8509, uu____8510)  in
          EFlat uu____8497
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8558 =
            let uu____8566 =
              assert_lid env1 e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8567 = translate_expr env1 e1  in
            (uu____8566, uu____8567, (FStar_Pervasives_Native.snd path))  in
          EField uu____8558
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8573 ->
          let uu____8584 =
            let uu____8586 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") e  in
            FStar_Util.format1 "todo: translate_expr [MLE_Let] (expr is: %s)"
              uu____8586
             in
          failwith uu____8584
      | FStar_Extraction_ML_Syntax.MLE_App (head,uu____8596) ->
          let uu____8601 =
            let uu____8603 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8603
             in
          failwith uu____8601
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8615 = FStar_List.map (translate_expr env1) seqs  in
          ESequence uu____8615
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8621 = FStar_List.map (translate_expr env1) es  in
          ETuple uu____8621
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8624,cons),es) ->
          let uu____8639 =
            let uu____8649 =
              assert_lid env1 e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8650 = FStar_List.map (translate_expr env1) es  in
            (uu____8649, cons, uu____8650)  in
          ECons uu____8639
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env1 args  in
          let env2 = add_binders env1 args  in
          let uu____8676 =
            let uu____8685 = translate_expr env2 body  in
            let uu____8686 =
              translate_type env2 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8685, uu____8686)  in
          EFun uu____8676
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8696 =
            let uu____8703 = translate_expr env1 e1  in
            let uu____8704 = translate_expr env1 e2  in
            let uu____8705 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env1 e31
               in
            (uu____8703, uu____8704, uu____8705)  in
          EIfThenElse uu____8696
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8707 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8715 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8731 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8749 =
              let uu____8764 = FStar_List.map (translate_type env1) ts  in
              (lid, uu____8764)  in
            TApp uu____8749
          else TQualified lid
      | uu____8779 ->
          let uu____8780 =
            let uu____8782 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8782
             in
          failwith uu____8780

and (translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)
      Prims.list -> (pattern * expr) Prims.list)
  =
  fun env1  ->
    fun branches1  -> FStar_List.map (translate_branch env1) branches1

and (translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) ->
      (pattern * expr))
  =
  fun env1  ->
    fun uu____8816  ->
      match uu____8816 with
      | (pat,guard,expr1) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8843 = translate_pat env1 pat  in
            (match uu____8843 with
             | (env2,pat1) ->
                 let uu____8854 = translate_expr env2 expr1  in
                 (pat1, uu____8854))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8862  ->
    match uu___7_8862 with
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
  fun env1  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env1, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env1, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Int (s,sw)) ->
          let uu____8929 =
            let uu____8930 =
              let uu____8936 = translate_width sw  in (uu____8936, s)  in
            PConstant uu____8930  in
          (env1, uu____8929)
      | FStar_Extraction_ML_Syntax.MLP_Var name1 ->
          let env2 = extend env1 name1  in
          (env2, (PVar { name = name1; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env2 = extend env1 "_"  in
          (env2, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8946,cons),ps) ->
          let uu____8961 =
            FStar_List.fold_left
              (fun uu____8981  ->
                 fun p1  ->
                   match uu____8981 with
                   | (env2,acc) ->
                       let uu____9001 = translate_pat env2 p1  in
                       (match uu____9001 with
                        | (env3,p2) -> (env3, (p2 :: acc)))) (env1, []) ps
             in
          (match uu____8961 with
           | (env2,ps1) -> (env2, (PCons (cons, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____9031,ps) ->
          let uu____9053 =
            FStar_List.fold_left
              (fun uu____9090  ->
                 fun uu____9091  ->
                   match (uu____9090, uu____9091) with
                   | ((env2,acc),(field,p1)) ->
                       let uu____9171 = translate_pat env2 p1  in
                       (match uu____9171 with
                        | (env3,p2) -> (env3, ((field, p2) :: acc))))
              (env1, []) ps
             in
          (match uu____9053 with
           | (env2,ps1) -> (env2, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____9242 =
            FStar_List.fold_left
              (fun uu____9262  ->
                 fun p1  ->
                   match uu____9262 with
                   | (env2,acc) ->
                       let uu____9282 = translate_pat env2 p1  in
                       (match uu____9282 with
                        | (env3,p2) -> (env3, (p2 :: acc)))) (env1, []) ps
             in
          (match uu____9242 with
           | (env2,ps1) -> (env2, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9309 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9315 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9329 =
            let uu____9331 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____9331
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____9329
          then
            let uu____9346 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9346
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9373) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9391 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9393 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        EConstant (CInt, s)

and (mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr)
  =
  fun env1  ->
    fun w  ->
      fun op1  ->
        fun args  ->
          let uu____9418 =
            let uu____9425 = FStar_List.map (translate_expr env1) args  in
            ((EOp (op1, w)), uu____9425)  in
          EApp uu____9418

let (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____9437  ->
    match uu____9437 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____9486 = m  in
               match uu____9486 with
               | (path,uu____9501,uu____9502) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___1671_9520  ->
                  match () with
                  | () ->
                      ((let uu____9524 =
                          let uu____9526 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____9526  in
                        if uu____9524
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____9532 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____9532))) ()
             with
             | uu___1670_9535 ->
                 ((let uu____9539 = FStar_Util.print_exn uu___1670_9535  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____9539);
                  FStar_Pervasives_Native.None)) modules
  