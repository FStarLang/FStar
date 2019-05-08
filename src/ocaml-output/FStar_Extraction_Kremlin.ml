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
  | DExternal of (cc FStar_Pervasives_Native.option * flag Prims.list *
  (Prims.string Prims.list * Prims.string) * typ) 
  | DTypeVariant of ((Prims.string Prims.list * Prims.string) * flag
  Prims.list * Prims.int * (Prims.string * (Prims.string * (typ *
  Prims.bool)) Prims.list) Prims.list) 
  | DTypeAbstractStruct of (Prims.string Prims.list * Prims.string) 
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
    match projectee with | DGlobal _0 -> true | uu____702 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____813 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____938 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1045 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1177 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1294 -> false
  
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
    | uu____1435 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1477 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1488 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1499 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1510 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1521 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1532 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1543 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1554 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1567 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1588 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1601 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1624 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1647 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1668 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1679 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1690 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1701 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1712 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1723 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1736 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1766 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1814 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1847 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1865 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1908 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1951 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1994 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2033 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2062 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2099 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2140 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2177 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2218 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2259 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2318 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2371 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2406 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2436 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2447 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2460 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2481 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2492 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2504 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2534 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2593 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2637 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2674 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2713 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2747 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2799 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2837 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2867 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2911 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2933 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____2956 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2986 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2997 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3008 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3019 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3030 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3041 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3052 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3063 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3074 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3085 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3096 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3107 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3118 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3129 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3140 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3151 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3162 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3173 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3184 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3195 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3206 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3217 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3228 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3239 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3250 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3261 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3274 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3296 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3322 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3364 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3396 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3441 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3474 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3485 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3496 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3507 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3518 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3529 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3540 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3551 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3562 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3573 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3622 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3641 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3659 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3679 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____3721 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____3732 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____3748 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____3780 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____3816 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____3879 -> false
  
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
  'Auu____3980 'Auu____3981 'Auu____3982 .
    ('Auu____3980 * 'Auu____3981 * 'Auu____3982) -> 'Auu____3980
  = fun uu____3993  -> match uu____3993 with | (x,uu____4001,uu____4002) -> x 
let snd3 :
  'Auu____4012 'Auu____4013 'Auu____4014 .
    ('Auu____4012 * 'Auu____4013 * 'Auu____4014) -> 'Auu____4013
  = fun uu____4025  -> match uu____4025 with | (uu____4032,x,uu____4034) -> x 
let thd3 :
  'Auu____4044 'Auu____4045 'Auu____4046 .
    ('Auu____4044 * 'Auu____4045 * 'Auu____4046) -> 'Auu____4046
  = fun uu____4057  -> match uu____4057 with | (uu____4064,uu____4065,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4075  ->
    match uu___0_4075 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4087 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4097  ->
    match uu___1_4097 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4106 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4127  ->
    match uu___2_4127 with
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
    | uu____4172 -> FStar_Pervasives_Native.None
  
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
      let uu___162_4328 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___162_4328.names_t);
        module_name = (uu___162_4328.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___166_4342 = env  in
      {
        names = (uu___166_4342.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___166_4342.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4357 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4357 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___177_4381  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___176_4388 ->
          let uu____4390 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4390
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___186_4410  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___185_4419 ->
          let uu____4421 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4421
  
let add_binders :
  'Auu____4432 . env -> (Prims.string * 'Auu____4432) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4467  ->
             match uu____4467 with | (name,uu____4474) -> extend env1 name)
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
      | uu____4526 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____4745  ->
    match uu____4745 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____4794 = m  in
               match uu____4794 with
               | (path,uu____4809,uu____4810) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___228_4828  ->
                  match () with
                  | () ->
                      ((let uu____4832 =
                          let uu____4834 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____4834  in
                        if uu____4832
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____4840 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____4840))) ()
             with
             | e ->
                 ((let uu____4849 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____4849);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____4852  ->
    match uu____4852 with
    | (module_name,modul,uu____4867) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____4902 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_4916  ->
         match uu___3_4916 with
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
         | uu____4927 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____4931 =
      FStar_List.choose
        (fun uu___4_4938  ->
           match uu___4_4938 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____4945 -> FStar_Pervasives_Native.None) flags
       in
    match uu____4931 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____4958 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____4972 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4974 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____4979) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5006;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5009;_} when
            FStar_Util.for_some
              (fun uu___5_5014  ->
                 match uu___5_5014 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5017 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____5038 =
                let uu____5039 =
                  let uu____5060 = translate_cc meta  in
                  let uu____5063 = translate_flags meta  in
                  let uu____5066 = translate_type env t0  in
                  (uu____5060, uu____5063, name1, uu____5066)  in
                DExternal uu____5039  in
              FStar_Pervasives_Native.Some uu____5038
            else
              ((let uu____5082 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5082);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5088;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5091;
                FStar_Extraction_ML_Syntax.loc = uu____5092;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5094;_} ->
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
               let rec find_return_type eff i uu___6_5151 =
                 match uu___6_5151 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5160,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5180 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5180 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5206 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5206 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5224) ->
                           let uu____5225 = translate_flags meta  in
                           MustDisappear :: uu____5225
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5228 = translate_flags meta  in
                           MustDisappear :: uu____5228
                       | uu____5231 -> translate_flags meta  in
                     try
                       (fun uu___368_5240  ->
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
                         ((let uu____5272 =
                             let uu____5278 =
                               let uu____5280 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5280 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5278)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5272);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5306;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5309;_} ->
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
                 (fun uu___395_5346  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5370 =
                       let uu____5376 =
                         let uu____5378 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5380 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5378
                           uu____5380
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5376)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5370);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5398;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5399;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5400;
            FStar_Extraction_ML_Syntax.print_typ = uu____5401;_} ->
            ((let uu____5408 =
                let uu____5414 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5414)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5408);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5421 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5421
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5435 = ty  in
      match uu____5435 with
      | (uu____5438,uu____5439,uu____5440,uu____5441,flags,uu____5443) ->
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
                     (let uu____5517 =
                        let uu____5518 =
                          let uu____5538 = translate_flags flags1  in
                          let uu____5541 = translate_type env1 t  in
                          (name1, uu____5538, (FStar_List.length args),
                            uu____5541)
                           in
                        DTypeAlias uu____5518  in
                      FStar_Pervasives_Native.Some uu____5517)
             | (uu____5554,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5599 =
                   let uu____5600 =
                     let uu____5632 = translate_flags flags1  in
                     let uu____5635 =
                       FStar_List.map
                         (fun uu____5667  ->
                            match uu____5667 with
                            | (f,t) ->
                                let uu____5687 =
                                  let uu____5693 = translate_type env1 t  in
                                  (uu____5693, false)  in
                                (f, uu____5687)) fields
                        in
                     (name1, uu____5632, (FStar_List.length args),
                       uu____5635)
                      in
                   DTypeFlat uu____5600  in
                 FStar_Pervasives_Native.Some uu____5599
             | (uu____5726,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____5776 =
                   let uu____5777 =
                     let uu____5816 =
                       FStar_List.map
                         (fun uu____5869  ->
                            match uu____5869 with
                            | (cons1,ts) ->
                                let uu____5917 =
                                  FStar_List.map
                                    (fun uu____5949  ->
                                       match uu____5949 with
                                       | (name2,t) ->
                                           let uu____5969 =
                                             let uu____5975 =
                                               translate_type env1 t  in
                                             (uu____5975, false)  in
                                           (name2, uu____5969)) ts
                                   in
                                (cons1, uu____5917)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____5816)
                      in
                   DTypeVariant uu____5777  in
                 FStar_Pervasives_Native.Some uu____5776
             | (uu____6028,name,_mangled_name,uu____6031,uu____6032,uu____6033)
                 ->
                 ((let uu____6049 =
                     let uu____6055 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6055)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6049);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6063 = find_t env name  in TBound uu____6063
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6066,t2) ->
          let uu____6068 =
            let uu____6073 = translate_type env t1  in
            let uu____6074 = translate_type env t2  in
            (uu____6073, uu____6074)  in
          TArrow uu____6068
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6078 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6078 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6085 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6085 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6102 = FStar_Util.must (mk_width m)  in TInt uu____6102
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6116 = FStar_Util.must (mk_width m)  in TInt uu____6116
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6121 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6121 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6125::arg::uu____6127::[],p) when
          (((let uu____6133 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6133 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6138 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6138 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6143 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6143 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6148 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6148 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6152 = translate_type env arg  in TBuf uu____6152
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6154::[],p) when
          ((((((((((let uu____6160 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6160 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6165 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6165 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6170 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6170 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6175 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6175 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6180 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6180 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6185 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6185 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6190 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6190 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6195 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6195 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6200 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6200 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6205 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6205 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6210 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6210 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6214 = translate_type env arg  in TBuf uu____6214
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6216::uu____6217::[],p) when
          let uu____6221 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6221 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6225 = translate_type env arg  in TBuf uu____6225
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6232 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6232 = "FStar.Buffer.buffer") ||
                        (let uu____6237 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6237 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6242 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6242 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6247 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6247 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6252 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6252 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6257 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6257 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6262 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6262 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6267 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6267 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6272 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6272 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6277 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6277 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6282 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6282 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6287 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6287 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6292 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6292 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6297 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6297 = "FStar.HyperStack.ST.mmref")
          -> let uu____6301 = translate_type env arg  in TBuf uu____6301
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6302::arg::[],p) when
          (let uu____6309 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6309 = "FStar.HyperStack.s_ref") ||
            (let uu____6314 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6314 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6318 = translate_type env arg  in TBuf uu____6318
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6319::[],p) when
          let uu____6323 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6323 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6375 = FStar_List.map (translate_type env) args  in
          TTuple uu____6375
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____6386 =
              let uu____6401 = FStar_List.map (translate_type env) args  in
              (lid, uu____6401)  in
            TApp uu____6386
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6419 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6419

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
    fun uu____6437  ->
      match uu____6437 with
      | (name,typ) ->
          let uu____6447 = translate_type env typ  in
          { name; typ = uu____6447; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6454 = find env name  in EBound uu____6454
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6468 =
            let uu____6473 = FStar_Util.must (mk_op op)  in
            let uu____6474 = FStar_Util.must (mk_width m)  in
            (uu____6473, uu____6474)  in
          EOp uu____6468
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6484 =
            let uu____6489 = FStar_Util.must (mk_bool_op op)  in
            (uu____6489, Bool)  in
          EOp uu____6484
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
            let uu____6512 = translate_type env typ  in
            { name; typ = uu____6512; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6539 =
            let uu____6550 = translate_expr env expr  in
            let uu____6551 = translate_branches env branches  in
            (uu____6550, uu____6551)  in
          EMatch uu____6539
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6565;
                  FStar_Extraction_ML_Syntax.loc = uu____6566;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6568;
             FStar_Extraction_ML_Syntax.loc = uu____6569;_},arg::[])
          when
          let uu____6575 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6575 = "FStar.Dyn.undyn" ->
          let uu____6579 =
            let uu____6584 = translate_expr env arg  in
            let uu____6585 = translate_type env t  in
            (uu____6584, uu____6585)  in
          ECast uu____6579
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6587;
                  FStar_Extraction_ML_Syntax.loc = uu____6588;_},uu____6589);
             FStar_Extraction_ML_Syntax.mlty = uu____6590;
             FStar_Extraction_ML_Syntax.loc = uu____6591;_},uu____6592)
          when
          let uu____6601 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6601 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6606;
                  FStar_Extraction_ML_Syntax.loc = uu____6607;_},uu____6608);
             FStar_Extraction_ML_Syntax.mlty = uu____6609;
             FStar_Extraction_ML_Syntax.loc = uu____6610;_},arg::[])
          when
          ((let uu____6620 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6620 = "FStar.HyperStack.All.failwith") ||
             (let uu____6625 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6625 = "FStar.Error.unexpected"))
            ||
            (let uu____6630 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6630 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6635;
               FStar_Extraction_ML_Syntax.loc = uu____6636;_} -> EAbortS msg
           | uu____6638 ->
               let print7 =
                 let uu____6640 =
                   let uu____6641 =
                     let uu____6642 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6642
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6641  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6640
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6649;
                  FStar_Extraction_ML_Syntax.loc = uu____6650;_},uu____6651);
             FStar_Extraction_ML_Syntax.mlty = uu____6652;
             FStar_Extraction_ML_Syntax.loc = uu____6653;_},e1::[])
          when
          (let uu____6663 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6663 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6668 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6668 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6673;
                  FStar_Extraction_ML_Syntax.loc = uu____6674;_},uu____6675);
             FStar_Extraction_ML_Syntax.mlty = uu____6676;
             FStar_Extraction_ML_Syntax.loc = uu____6677;_},e1::e2::[])
          when
          (((let uu____6688 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6688 = "FStar.Buffer.index") ||
              (let uu____6693 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6693 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____6698 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6698 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____6703 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6703 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____6707 =
            let uu____6712 = translate_expr env e1  in
            let uu____6713 = translate_expr env e2  in
            (uu____6712, uu____6713)  in
          EBufRead uu____6707
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6715;
                  FStar_Extraction_ML_Syntax.loc = uu____6716;_},uu____6717);
             FStar_Extraction_ML_Syntax.mlty = uu____6718;
             FStar_Extraction_ML_Syntax.loc = uu____6719;_},e1::[])
          when
          let uu____6727 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6727 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6731 =
            let uu____6736 = translate_expr env e1  in
            (uu____6736, (EConstant (UInt32, "0")))  in
          EBufRead uu____6731
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
             FStar_Extraction_ML_Syntax.loc = uu____6744;_},e1::e2::[])
          when
          ((let uu____6755 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6755 = "FStar.Buffer.create") ||
             (let uu____6760 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6760 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____6765 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6765 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____6769 =
            let uu____6776 = translate_expr env e1  in
            let uu____6777 = translate_expr env e2  in
            (Stack, uu____6776, uu____6777)  in
          EBufCreate uu____6769
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6779;
                  FStar_Extraction_ML_Syntax.loc = uu____6780;_},uu____6781);
             FStar_Extraction_ML_Syntax.mlty = uu____6782;
             FStar_Extraction_ML_Syntax.loc = uu____6783;_},elen::[])
          when
          let uu____6791 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6791 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____6795 =
            let uu____6800 = translate_expr env elen  in (Stack, uu____6800)
             in
          EBufCreateNoInit uu____6795
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
             FStar_Extraction_ML_Syntax.loc = uu____6806;_},init1::[])
          when
          let uu____6814 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6814 = "FStar.HyperStack.ST.salloc" ->
          let uu____6818 =
            let uu____6825 = translate_expr env init1  in
            (Stack, uu____6825, (EConstant (UInt32, "1")))  in
          EBufCreate uu____6818
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6829;
                  FStar_Extraction_ML_Syntax.loc = uu____6830;_},uu____6831);
             FStar_Extraction_ML_Syntax.mlty = uu____6832;
             FStar_Extraction_ML_Syntax.loc = uu____6833;_},e2::[])
          when
          ((let uu____6843 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6843 = "FStar.Buffer.createL") ||
             (let uu____6848 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6848 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____6853 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6853 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____6857 =
            let uu____6864 =
              let uu____6867 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____6867  in
            (Stack, uu____6864)  in
          EBufCreateL uu____6857
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
             FStar_Extraction_ML_Syntax.loc = uu____6877;_},_erid::e2::[])
          when
          (let uu____6888 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6888 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____6893 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6893 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____6897 =
            let uu____6904 =
              let uu____6907 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____6907  in
            (Eternal, uu____6904)  in
          EBufCreateL uu____6897
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6913;
                  FStar_Extraction_ML_Syntax.loc = uu____6914;_},uu____6915);
             FStar_Extraction_ML_Syntax.mlty = uu____6916;
             FStar_Extraction_ML_Syntax.loc = uu____6917;_},_rid::init1::[])
          when
          let uu____6926 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6926 = "FStar.HyperStack.ST.ralloc" ->
          let uu____6930 =
            let uu____6937 = translate_expr env init1  in
            (Eternal, uu____6937, (EConstant (UInt32, "1")))  in
          EBufCreate uu____6930
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
             FStar_Extraction_ML_Syntax.loc = uu____6945;_},_e0::e1::e2::[])
          when
          ((let uu____6957 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6957 = "FStar.Buffer.rcreate") ||
             (let uu____6962 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6962 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____6967 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6967 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____6971 =
            let uu____6978 = translate_expr env e1  in
            let uu____6979 = translate_expr env e2  in
            (Eternal, uu____6978, uu____6979)  in
          EBufCreate uu____6971
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6981;
                  FStar_Extraction_ML_Syntax.loc = uu____6982;_},uu____6983);
             FStar_Extraction_ML_Syntax.mlty = uu____6984;
             FStar_Extraction_ML_Syntax.loc = uu____6985;_},_erid::elen::[])
          when
          let uu____6994 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6994 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____6998 =
            let uu____7003 = translate_expr env elen  in
            (Eternal, uu____7003)  in
          EBufCreateNoInit uu____6998
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7005;
                  FStar_Extraction_ML_Syntax.loc = uu____7006;_},uu____7007);
             FStar_Extraction_ML_Syntax.mlty = uu____7008;
             FStar_Extraction_ML_Syntax.loc = uu____7009;_},_rid::init1::[])
          when
          let uu____7018 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7018 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7022 =
            let uu____7029 = translate_expr env init1  in
            (ManuallyManaged, uu____7029, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7022
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7033;
                  FStar_Extraction_ML_Syntax.loc = uu____7034;_},uu____7035);
             FStar_Extraction_ML_Syntax.mlty = uu____7036;
             FStar_Extraction_ML_Syntax.loc = uu____7037;_},_e0::e1::e2::[])
          when
          (((let uu____7049 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7049 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7054 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7054 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7059 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7059 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7064 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7064 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7068 =
            let uu____7075 = translate_expr env e1  in
            let uu____7076 = translate_expr env e2  in
            (ManuallyManaged, uu____7075, uu____7076)  in
          EBufCreate uu____7068
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7078;
                  FStar_Extraction_ML_Syntax.loc = uu____7079;_},uu____7080);
             FStar_Extraction_ML_Syntax.mlty = uu____7081;
             FStar_Extraction_ML_Syntax.loc = uu____7082;_},_erid::elen::[])
          when
          let uu____7091 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7091 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7095 =
            let uu____7100 = translate_expr env elen  in
            (ManuallyManaged, uu____7100)  in
          EBufCreateNoInit uu____7095
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7102;
                  FStar_Extraction_ML_Syntax.loc = uu____7103;_},uu____7104);
             FStar_Extraction_ML_Syntax.mlty = uu____7105;
             FStar_Extraction_ML_Syntax.loc = uu____7106;_},e2::[])
          when
          let uu____7114 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7114 = "FStar.HyperStack.ST.rfree" ->
          let uu____7118 = translate_expr env e2  in EBufFree uu____7118
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7120;
                  FStar_Extraction_ML_Syntax.loc = uu____7121;_},uu____7122);
             FStar_Extraction_ML_Syntax.mlty = uu____7123;
             FStar_Extraction_ML_Syntax.loc = uu____7124;_},e2::[])
          when
          (let uu____7134 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7134 = "FStar.Buffer.rfree") ||
            (let uu____7139 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7139 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7143 = translate_expr env e2  in EBufFree uu____7143
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
             FStar_Extraction_ML_Syntax.loc = uu____7149;_},e1::e2::_e3::[])
          when
          let uu____7159 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7159 = "FStar.Buffer.sub" ->
          let uu____7163 =
            let uu____7168 = translate_expr env e1  in
            let uu____7169 = translate_expr env e2  in
            (uu____7168, uu____7169)  in
          EBufSub uu____7163
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
             FStar_Extraction_ML_Syntax.loc = uu____7175;_},e1::e2::_e3::[])
          when
          let uu____7185 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7185 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____7189 =
            let uu____7194 = translate_expr env e1  in
            let uu____7195 = translate_expr env e2  in
            (uu____7194, uu____7195)  in
          EBufSub uu____7189
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7197;
                  FStar_Extraction_ML_Syntax.loc = uu____7198;_},uu____7199);
             FStar_Extraction_ML_Syntax.mlty = uu____7200;
             FStar_Extraction_ML_Syntax.loc = uu____7201;_},e1::e2::[])
          when
          let uu____7210 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7210 = "FStar.Buffer.join" -> translate_expr env e1
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
             FStar_Extraction_ML_Syntax.loc = uu____7219;_},e1::e2::[])
          when
          let uu____7228 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7228 = "FStar.Buffer.offset" ->
          let uu____7232 =
            let uu____7237 = translate_expr env e1  in
            let uu____7238 = translate_expr env e2  in
            (uu____7237, uu____7238)  in
          EBufSub uu____7232
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7240;
                  FStar_Extraction_ML_Syntax.loc = uu____7241;_},uu____7242);
             FStar_Extraction_ML_Syntax.mlty = uu____7243;
             FStar_Extraction_ML_Syntax.loc = uu____7244;_},e1::e2::[])
          when
          let uu____7253 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7253 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7257 =
            let uu____7262 = translate_expr env e1  in
            let uu____7263 = translate_expr env e2  in
            (uu____7262, uu____7263)  in
          EBufSub uu____7257
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7265;
                  FStar_Extraction_ML_Syntax.loc = uu____7266;_},uu____7267);
             FStar_Extraction_ML_Syntax.mlty = uu____7268;
             FStar_Extraction_ML_Syntax.loc = uu____7269;_},e1::e2::e3::[])
          when
          (((let uu____7281 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7281 = "FStar.Buffer.upd") ||
              (let uu____7286 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7286 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7291 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7291 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7296 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7296 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7300 =
            let uu____7307 = translate_expr env e1  in
            let uu____7308 = translate_expr env e2  in
            let uu____7309 = translate_expr env e3  in
            (uu____7307, uu____7308, uu____7309)  in
          EBufWrite uu____7300
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7311;
                  FStar_Extraction_ML_Syntax.loc = uu____7312;_},uu____7313);
             FStar_Extraction_ML_Syntax.mlty = uu____7314;
             FStar_Extraction_ML_Syntax.loc = uu____7315;_},e1::e2::[])
          when
          let uu____7324 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7324 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7328 =
            let uu____7335 = translate_expr env e1  in
            let uu____7336 = translate_expr env e2  in
            (uu____7335, (EConstant (UInt32, "0")), uu____7336)  in
          EBufWrite uu____7328
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7340;
             FStar_Extraction_ML_Syntax.loc = uu____7341;_},uu____7342::[])
          when
          let uu____7345 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7345 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7350;
             FStar_Extraction_ML_Syntax.loc = uu____7351;_},uu____7352::[])
          when
          let uu____7355 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7355 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7360;
                  FStar_Extraction_ML_Syntax.loc = uu____7361;_},uu____7362);
             FStar_Extraction_ML_Syntax.mlty = uu____7363;
             FStar_Extraction_ML_Syntax.loc = uu____7364;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7378 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7378 = "FStar.Buffer.blit") ||
             (let uu____7383 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7383 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7388 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7388 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7392 =
            let uu____7403 = translate_expr env e1  in
            let uu____7404 = translate_expr env e2  in
            let uu____7405 = translate_expr env e3  in
            let uu____7406 = translate_expr env e4  in
            let uu____7407 = translate_expr env e5  in
            (uu____7403, uu____7404, uu____7405, uu____7406, uu____7407)  in
          EBufBlit uu____7392
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
             FStar_Extraction_ML_Syntax.loc = uu____7413;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7429 =
            let uu____7436 = translate_expr env e1  in
            let uu____7437 = translate_expr env e2  in
            let uu____7438 = translate_expr env e3  in
            (uu____7436, uu____7437, uu____7438)  in
          EBufFill uu____7429
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7440;
             FStar_Extraction_ML_Syntax.loc = uu____7441;_},uu____7442::[])
          when
          let uu____7445 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7445 = "FStar.HyperStack.ST.get" -> EUnit
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
             FStar_Extraction_ML_Syntax.loc = uu____7454;_},_ebuf::_eseq::[])
          when
          (((let uu____7465 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7465 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7470 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7470 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7475 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7475 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7480 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7480 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7485;
             FStar_Extraction_ML_Syntax.loc = uu____7486;_},e1::[])
          when
          let uu____7490 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7490 = "Obj.repr" ->
          let uu____7494 =
            let uu____7499 = translate_expr env e1  in (uu____7499, TAny)  in
          ECast uu____7494
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7502;
             FStar_Extraction_ML_Syntax.loc = uu____7503;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7519 = FStar_Util.must (mk_width m)  in
          let uu____7520 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7519 uu____7520 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7522;
             FStar_Extraction_ML_Syntax.loc = uu____7523;_},args)
          when is_bool_op op ->
          let uu____7537 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7537 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7539;
             FStar_Extraction_ML_Syntax.loc = uu____7540;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7542;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7543;_}::[])
          when is_machine_int m ->
          let uu____7568 =
            let uu____7574 = FStar_Util.must (mk_width m)  in (uu____7574, c)
             in
          EConstant uu____7568
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7577;
             FStar_Extraction_ML_Syntax.loc = uu____7578;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7580;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7581;_}::[])
          when is_machine_int m ->
          let uu____7606 =
            let uu____7612 = FStar_Util.must (mk_width m)  in (uu____7612, c)
             in
          EConstant uu____7606
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7614;
             FStar_Extraction_ML_Syntax.loc = uu____7615;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7617;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7618;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7631 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7633;
             FStar_Extraction_ML_Syntax.loc = uu____7634;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7636;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7637;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7654 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7656;
             FStar_Extraction_ML_Syntax.loc = uu____7657;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7659;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7660;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7675 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7677;
             FStar_Extraction_ML_Syntax.loc = uu____7678;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7680;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7681;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____7696 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____7699;
             FStar_Extraction_ML_Syntax.loc = uu____7700;_},arg::[])
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
            let uu____7728 =
              let uu____7733 = translate_expr env arg  in
              (uu____7733, (TInt UInt64))  in
            ECast uu____7728
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____7738 =
                 let uu____7743 = translate_expr env arg  in
                 (uu____7743, (TInt UInt32))  in
               ECast uu____7738)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____7748 =
                   let uu____7753 = translate_expr env arg  in
                   (uu____7753, (TInt UInt16))  in
                 ECast uu____7748)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____7758 =
                     let uu____7763 = translate_expr env arg  in
                     (uu____7763, (TInt UInt8))  in
                   ECast uu____7758)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____7768 =
                       let uu____7773 = translate_expr env arg  in
                       (uu____7773, (TInt Int64))  in
                     ECast uu____7768)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____7778 =
                         let uu____7783 = translate_expr env arg  in
                         (uu____7783, (TInt Int32))  in
                       ECast uu____7778)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____7788 =
                           let uu____7793 = translate_expr env arg  in
                           (uu____7793, (TInt Int16))  in
                         ECast uu____7788)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____7798 =
                             let uu____7803 = translate_expr env arg  in
                             (uu____7803, (TInt Int8))  in
                           ECast uu____7798)
                        else
                          (let uu____7806 =
                             let uu____7813 =
                               let uu____7816 = translate_expr env arg  in
                               [uu____7816]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____7813)
                              in
                           EApp uu____7806)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____7836 =
            let uu____7843 = translate_expr env head1  in
            let uu____7844 = FStar_List.map (translate_expr env) args  in
            (uu____7843, uu____7844)  in
          EApp uu____7836
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____7855 =
            let uu____7862 = translate_expr env head1  in
            let uu____7863 = FStar_List.map (translate_type env) ty_args  in
            (uu____7862, uu____7863)  in
          ETypApp uu____7855
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____7871 =
            let uu____7876 = translate_expr env e1  in
            let uu____7877 = translate_type env t_to  in
            (uu____7876, uu____7877)  in
          ECast uu____7871
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____7878,fields) ->
          let uu____7900 =
            let uu____7912 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____7913 =
              FStar_List.map
                (fun uu____7935  ->
                   match uu____7935 with
                   | (field,expr) ->
                       let uu____7950 = translate_expr env expr  in
                       (field, uu____7950)) fields
               in
            (uu____7912, uu____7913)  in
          EFlat uu____7900
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____7961 =
            let uu____7969 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____7970 = translate_expr env e1  in
            (uu____7969, uu____7970, (FStar_Pervasives_Native.snd path))  in
          EField uu____7961
      | FStar_Extraction_ML_Syntax.MLE_Let uu____7976 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____7989) ->
          let uu____7994 =
            let uu____7996 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____7996
             in
          failwith uu____7994
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8008 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8008
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8014 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8014
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8017,cons1),es) ->
          let uu____8032 =
            let uu____8042 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8043 = FStar_List.map (translate_expr env) es  in
            (uu____8042, cons1, uu____8043)  in
          ECons uu____8032
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8069 =
            let uu____8078 = translate_expr env1 body  in
            let uu____8079 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8078, uu____8079)  in
          EFun uu____8069
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8089 =
            let uu____8096 = translate_expr env e1  in
            let uu____8097 = translate_expr env e2  in
            let uu____8098 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8096, uu____8097, uu____8098)  in
          EIfThenElse uu____8089
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8100 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8108 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8124 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____8142 =
              let uu____8157 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8157)  in
            TApp uu____8142
          else TQualified lid
      | uu____8172 ->
          let uu____8173 =
            let uu____8175 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8175
             in
          failwith uu____8173

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
    fun uu____8209  ->
      match uu____8209 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8236 = translate_pat env pat  in
            (match uu____8236 with
             | (env1,pat1) ->
                 let uu____8247 = translate_expr env1 expr  in
                 (pat1, uu____8247))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8255  ->
    match uu___7_8255 with
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
          let uu____8322 =
            let uu____8323 =
              let uu____8329 = translate_width sw  in (uu____8329, s)  in
            PConstant uu____8323  in
          (env, uu____8322)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8339,cons1),ps) ->
          let uu____8354 =
            FStar_List.fold_left
              (fun uu____8374  ->
                 fun p1  ->
                   match uu____8374 with
                   | (env1,acc) ->
                       let uu____8394 = translate_pat env1 p1  in
                       (match uu____8394 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8354 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8424,ps) ->
          let uu____8446 =
            FStar_List.fold_left
              (fun uu____8483  ->
                 fun uu____8484  ->
                   match (uu____8483, uu____8484) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____8564 = translate_pat env1 p1  in
                       (match uu____8564 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8446 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____8635 =
            FStar_List.fold_left
              (fun uu____8655  ->
                 fun p1  ->
                   match uu____8655 with
                   | (env1,acc) ->
                       let uu____8675 = translate_pat env1 p1  in
                       (match uu____8675 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8635 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____8702 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____8708 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____8722 =
            let uu____8724 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____8724
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____8722
          then
            let uu____8739 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____8739
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____8766) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____8784 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____8786 ->
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
          let uu____8810 =
            let uu____8817 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____8817)  in
          EApp uu____8810
