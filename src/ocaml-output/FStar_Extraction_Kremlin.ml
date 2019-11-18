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
  | DUntaggedUnion of ((Prims.string Prims.list * Prims.string) * flag
  Prims.list * Prims.int * (Prims.string * typ) Prims.list) 
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
    match projectee with | DGlobal _0 -> true | uu____769 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____880 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____1005 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1112 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1244 -> false
  
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee  ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
  
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1361 -> false
  
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
    | uu____1502 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1570 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DUntaggedUnion : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DUntaggedUnion _0 -> true | uu____1690 -> false
  
let (__proj__DUntaggedUnion__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * typ) Prims.list))
  = fun projectee  -> match projectee with | DUntaggedUnion _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1786 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1797 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1808 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1819 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1830 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1841 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1852 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1863 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1876 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1897 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1910 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1933 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1956 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1977 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1988 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1999 -> false
  
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Deprecated _0 -> true | uu____2012 -> false
  
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Deprecated _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____2033 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____2044 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____2055 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____2068 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____2098 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____2146 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____2179 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____2197 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____2240 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____2283 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____2326 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2365 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2394 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2431 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2472 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2509 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2550 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2591 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2650 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2703 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2738 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2768 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2779 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2792 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2813 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2824 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2836 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2866 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2925 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2969 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____3006 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____3045 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____3079 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____3131 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____3169 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____3199 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____3243 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____3265 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____3288 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3318 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3329 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3340 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3351 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3362 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3373 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3384 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3395 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3406 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3417 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3428 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3439 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3450 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3461 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3472 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3483 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3494 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3505 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3516 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3527 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3538 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3549 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3560 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3571 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3582 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3593 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3606 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3628 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3654 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3696 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3728 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3773 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3806 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3817 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3828 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3839 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3850 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3861 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3872 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3883 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3894 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3905 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3954 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3973 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3991 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____4011 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____4053 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____4064 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____4080 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____4112 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____4148 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____4211 -> false
  
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
  'Auu____4312 'Auu____4313 'Auu____4314 .
    ('Auu____4312 * 'Auu____4313 * 'Auu____4314) -> 'Auu____4312
  = fun uu____4325  -> match uu____4325 with | (x,uu____4333,uu____4334) -> x 
let snd3 :
  'Auu____4344 'Auu____4345 'Auu____4346 .
    ('Auu____4344 * 'Auu____4345 * 'Auu____4346) -> 'Auu____4345
  = fun uu____4357  -> match uu____4357 with | (uu____4364,x,uu____4366) -> x 
let thd3 :
  'Auu____4376 'Auu____4377 'Auu____4378 .
    ('Auu____4376 * 'Auu____4377 * 'Auu____4378) -> 'Auu____4378
  = fun uu____4389  -> match uu____4389 with | (uu____4396,uu____4397,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4407  ->
    match uu___0_4407 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4419 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4429  ->
    match uu___1_4429 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4438 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4459  ->
    match uu___2_4459 with
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
    | uu____4504 -> FStar_Pervasives_Native.None
  
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
      let uu___165_4660 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___165_4660.names_t);
        module_name = (uu___165_4660.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___169_4674 = env  in
      {
        names = (uu___169_4674.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___169_4674.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4689 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4689 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___180_4713  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___179_4720 ->
          let uu____4722 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4722
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___189_4742  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___188_4751 ->
          let uu____4753 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4753
  
let add_binders :
  'Auu____4764 . env -> (Prims.string * 'Auu____4764) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4799  ->
             match uu____4799 with | (name,uu____4806) -> extend env1 name)
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
      | uu____4858 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____5077  ->
    match uu____5077 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____5126 = m  in
               match uu____5126 with
               | (path,uu____5141,uu____5142) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___231_5160  ->
                  match () with
                  | () ->
                      ((let uu____5164 =
                          let uu____5166 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____5166  in
                        if uu____5164
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____5172 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____5172))) ()
             with
             | e ->
                 ((let uu____5181 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____5181);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____5184  ->
    match uu____5184 with
    | (module_name,modul,uu____5199) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5234 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5248  ->
         match uu___3_5248 with
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
         | uu____5261 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5265 =
      FStar_List.choose
        (fun uu___4_5272  ->
           match uu___4_5272 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5279 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5265 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5292 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5306 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5308 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5313) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5340;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5343;_} when
            FStar_Util.for_some
              (fun uu___5_5348  ->
                 match uu___5_5348 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5351 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5374) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5396 -> []  in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____5404 =
                let uu____5405 =
                  let uu____5431 = translate_cc meta  in
                  let uu____5434 = translate_flags meta  in
                  let uu____5437 = translate_type env t0  in
                  (uu____5431, uu____5434, name1, uu____5437, arg_names)  in
                DExternal uu____5405  in
              FStar_Pervasives_Native.Some uu____5404
            else
              ((let uu____5456 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5456);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5462;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5465;
                FStar_Extraction_ML_Syntax.loc = uu____5466;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5468;_} ->
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
               let rec find_return_type eff i uu___6_5525 =
                 match uu___6_5525 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5534,eff1,t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5554 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5554 with
               | (i,eff,t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5580 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5580 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5598) ->
                           let uu____5599 = translate_flags meta  in
                           MustDisappear :: uu____5599
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5602 = translate_flags meta  in
                           MustDisappear :: uu____5602
                       | uu____5605 -> translate_flags meta  in
                     try
                       (fun uu___379_5614  ->
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
                         ((let uu____5646 =
                             let uu____5652 =
                               let uu____5654 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5654 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5652)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5646);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5680;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5683;_} ->
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
                 (fun uu___406_5720  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5744 =
                       let uu____5750 =
                         let uu____5752 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5754 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5752
                           uu____5754
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5750)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5744);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5772;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5773;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5774;
            FStar_Extraction_ML_Syntax.print_typ = uu____5775;_} ->
            ((let uu____5782 =
                let uu____5788 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5788)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5782);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5795 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5795
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5809 = ty  in
      match uu____5809 with
      | (uu____5812,uu____5813,uu____5814,uu____5815,flags,uu____5817) ->
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
                     (let uu____5891 =
                        let uu____5892 =
                          let uu____5912 = translate_flags flags1  in
                          let uu____5915 = translate_type env1 t  in
                          (name1, uu____5912, (FStar_List.length args),
                            uu____5915)
                           in
                        DTypeAlias uu____5892  in
                      FStar_Pervasives_Native.Some uu____5891)
             | (uu____5928,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5973 =
                   let uu____5974 =
                     let uu____6006 = translate_flags flags1  in
                     let uu____6009 =
                       FStar_List.map
                         (fun uu____6041  ->
                            match uu____6041 with
                            | (f,t) ->
                                let uu____6061 =
                                  let uu____6067 = translate_type env1 t  in
                                  (uu____6067, false)  in
                                (f, uu____6061)) fields
                        in
                     (name1, uu____6006, (FStar_List.length args),
                       uu____6009)
                      in
                   DTypeFlat uu____5974  in
                 FStar_Pervasives_Native.Some uu____5973
             | (uu____6100,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____6150 =
                   let uu____6151 =
                     let uu____6190 =
                       FStar_List.map
                         (fun uu____6243  ->
                            match uu____6243 with
                            | (cons1,ts) ->
                                let uu____6291 =
                                  FStar_List.map
                                    (fun uu____6323  ->
                                       match uu____6323 with
                                       | (name2,t) ->
                                           let uu____6343 =
                                             let uu____6349 =
                                               translate_type env1 t  in
                                             (uu____6349, false)  in
                                           (name2, uu____6343)) ts
                                   in
                                (cons1, uu____6291)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____6190)
                      in
                   DTypeVariant uu____6151  in
                 FStar_Pervasives_Native.Some uu____6150
             | (uu____6402,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Union (cases,uu____6408)))
                 ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____6453 =
                   let uu____6454 =
                     let uu____6481 =
                       FStar_List.map
                         (fun uu____6503  ->
                            match uu____6503 with
                            | (f,t) ->
                                let uu____6518 = translate_type env1 t  in
                                (f, uu____6518)) cases
                        in
                     (name1, flags2, (FStar_List.length args), uu____6481)
                      in
                   DUntaggedUnion uu____6454  in
                 FStar_Pervasives_Native.Some uu____6453
             | (uu____6539,name,_mangled_name,uu____6542,uu____6543,uu____6544)
                 ->
                 ((let uu____6560 =
                     let uu____6566 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6566)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6560);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6574 = find_t env name  in TBound uu____6574
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6577,t2) ->
          let uu____6579 =
            let uu____6584 = translate_type env t1  in
            let uu____6585 = translate_type env t2  in
            (uu____6584, uu____6585)  in
          TArrow uu____6579
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6589 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6589 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6596 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6596 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6613 = FStar_Util.must (mk_width m)  in TInt uu____6613
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6627 = FStar_Util.must (mk_width m)  in TInt uu____6627
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6632 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6632 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6636::arg::uu____6638::[],p) when
          (((let uu____6644 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6644 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6649 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6649 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6654 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6654 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6659 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6659 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6663 = translate_type env arg  in TBuf uu____6663
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6665::[],p) when
          ((((((((((let uu____6671 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6671 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6676 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6676 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6681 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6681 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6686 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6686 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6691 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6691 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6696 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6696 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6701 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6701 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6706 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6706 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6711 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6711 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6716 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6716 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6721 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6721 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6725 = translate_type env arg  in TBuf uu____6725
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6727::uu____6728::[],p) when
          let uu____6732 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6732 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6736 = translate_type env arg  in TBuf uu____6736
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6741 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6741 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6745 = translate_type env arg  in TBuf uu____6745
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6752 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6752 = "FStar.Buffer.buffer") ||
                        (let uu____6757 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6757 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6762 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6762 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6767 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6767 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6772 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6772 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6777 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6777 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6782 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6782 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6787 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6787 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6792 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6792 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6797 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6797 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6802 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6802 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6807 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6807 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6812 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6812 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6817 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6817 = "FStar.HyperStack.ST.mmref")
          -> let uu____6821 = translate_type env arg  in TBuf uu____6821
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6822::arg::[],p) when
          (let uu____6829 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6829 = "FStar.HyperStack.s_ref") ||
            (let uu____6834 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6834 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6838 = translate_type env arg  in TBuf uu____6838
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6839::[],p) when
          let uu____6843 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6843 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6895 = FStar_List.map (translate_type env) args  in
          TTuple uu____6895
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6906 =
              let uu____6921 = FStar_List.map (translate_type env) args  in
              (lid, uu____6921)  in
            TApp uu____6906
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6939 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6939

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
    fun uu____6957  ->
      match uu____6957 with
      | (name,typ) ->
          let uu____6967 = translate_type env typ  in
          { name; typ = uu____6967; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6974 = find env name  in EBound uu____6974
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6988 =
            let uu____6993 = FStar_Util.must (mk_op op)  in
            let uu____6994 = FStar_Util.must (mk_width m)  in
            (uu____6993, uu____6994)  in
          EOp uu____6988
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____7004 =
            let uu____7009 = FStar_Util.must (mk_bool_op op)  in
            (uu____7009, Bool)  in
          EOp uu____7004
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
            let uu____7032 = translate_type env typ  in
            { name; typ = uu____7032; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____7059 =
            let uu____7070 = translate_expr env expr  in
            let uu____7071 = translate_branches env branches  in
            (uu____7070, uu____7071)  in
          EMatch uu____7059
      | FStar_Extraction_ML_Syntax.MLE_UCons (e0,f) ->
          let uu____7088 =
            let uu____7100 =
              translate_type env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____7101 =
              let uu____7109 =
                let uu____7115 = translate_expr env e0  in (f, uu____7115)
                 in
              [uu____7109]  in
            (uu____7100, uu____7101)  in
          EFlat uu____7088
      | FStar_Extraction_ML_Syntax.MLE_UProj (e1,t,f) ->
          let uu____7139 =
            let uu____7147 = translate_type env t  in
            let uu____7148 = translate_expr env e1  in
            (uu____7147, uu____7148, f)  in
          EField uu____7139
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7151;
                  FStar_Extraction_ML_Syntax.loc = uu____7152;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7154;
             FStar_Extraction_ML_Syntax.loc = uu____7155;_},arg::[])
          when
          let uu____7161 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7161 = "FStar.Dyn.undyn" ->
          let uu____7165 =
            let uu____7170 = translate_expr env arg  in
            let uu____7171 = translate_type env t  in
            (uu____7170, uu____7171)  in
          ECast uu____7165
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7173;
                  FStar_Extraction_ML_Syntax.loc = uu____7174;_},uu____7175);
             FStar_Extraction_ML_Syntax.mlty = uu____7176;
             FStar_Extraction_ML_Syntax.loc = uu____7177;_},uu____7178)
          when
          let uu____7187 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7187 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7192;
                  FStar_Extraction_ML_Syntax.loc = uu____7193;_},uu____7194);
             FStar_Extraction_ML_Syntax.mlty = uu____7195;
             FStar_Extraction_ML_Syntax.loc = uu____7196;_},arg::[])
          when
          ((let uu____7206 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7206 = "FStar.HyperStack.All.failwith") ||
             (let uu____7211 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7211 = "FStar.Error.unexpected"))
            ||
            (let uu____7216 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7216 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____7221;
               FStar_Extraction_ML_Syntax.loc = uu____7222;_} -> EAbortS msg
           | uu____7224 ->
               let print7 =
                 let uu____7226 =
                   let uu____7227 =
                     let uu____7228 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____7228
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____7227  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____7226
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7235;
                  FStar_Extraction_ML_Syntax.loc = uu____7236;_},uu____7237);
             FStar_Extraction_ML_Syntax.mlty = uu____7238;
             FStar_Extraction_ML_Syntax.loc = uu____7239;_},e1::[])
          when
          (let uu____7249 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7249 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____7254 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7254 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7259;
                  FStar_Extraction_ML_Syntax.loc = uu____7260;_},uu____7261);
             FStar_Extraction_ML_Syntax.mlty = uu____7262;
             FStar_Extraction_ML_Syntax.loc = uu____7263;_},e1::e2::[])
          when
          ((((let uu____7274 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7274 = "FStar.Buffer.index") ||
               (let uu____7279 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7279 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____7284 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7284 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____7289 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7289 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____7294 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7294 = "LowStar.ConstBuffer.index")
          ->
          let uu____7298 =
            let uu____7303 = translate_expr env e1  in
            let uu____7304 = translate_expr env e2  in
            (uu____7303, uu____7304)  in
          EBufRead uu____7298
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7306;
                  FStar_Extraction_ML_Syntax.loc = uu____7307;_},uu____7308);
             FStar_Extraction_ML_Syntax.mlty = uu____7309;
             FStar_Extraction_ML_Syntax.loc = uu____7310;_},e1::[])
          when
          let uu____7318 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7318 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____7322 =
            let uu____7327 = translate_expr env e1  in
            (uu____7327, (EConstant (UInt32, "0")))  in
          EBufRead uu____7322
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
             FStar_Extraction_ML_Syntax.loc = uu____7335;_},e1::e2::[])
          when
          ((let uu____7346 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7346 = "FStar.Buffer.create") ||
             (let uu____7351 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7351 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7356 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7356 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7360 =
            let uu____7367 = translate_expr env e1  in
            let uu____7368 = translate_expr env e2  in
            (Stack, uu____7367, uu____7368)  in
          EBufCreate uu____7360
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7370;
                  FStar_Extraction_ML_Syntax.loc = uu____7371;_},uu____7372);
             FStar_Extraction_ML_Syntax.mlty = uu____7373;
             FStar_Extraction_ML_Syntax.loc = uu____7374;_},elen::[])
          when
          let uu____7382 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7382 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7386 =
            let uu____7391 = translate_expr env elen  in (Stack, uu____7391)
             in
          EBufCreateNoInit uu____7386
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7393;
                  FStar_Extraction_ML_Syntax.loc = uu____7394;_},uu____7395);
             FStar_Extraction_ML_Syntax.mlty = uu____7396;
             FStar_Extraction_ML_Syntax.loc = uu____7397;_},init1::[])
          when
          let uu____7405 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7405 = "FStar.HyperStack.ST.salloc" ->
          let uu____7409 =
            let uu____7416 = translate_expr env init1  in
            (Stack, uu____7416, (EConstant (UInt32, "1")))  in
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
             FStar_Extraction_ML_Syntax.loc = uu____7424;_},e2::[])
          when
          ((let uu____7434 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7434 = "FStar.Buffer.createL") ||
             (let uu____7439 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7439 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7444 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7444 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7448 =
            let uu____7455 =
              let uu____7458 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7458  in
            (Stack, uu____7455)  in
          EBufCreateL uu____7448
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7464;
                  FStar_Extraction_ML_Syntax.loc = uu____7465;_},uu____7466);
             FStar_Extraction_ML_Syntax.mlty = uu____7467;
             FStar_Extraction_ML_Syntax.loc = uu____7468;_},_erid::e2::[])
          when
          (let uu____7479 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7479 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7484 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7484 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7488 =
            let uu____7495 =
              let uu____7498 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7498  in
            (Eternal, uu____7495)  in
          EBufCreateL uu____7488
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7504;
                  FStar_Extraction_ML_Syntax.loc = uu____7505;_},uu____7506);
             FStar_Extraction_ML_Syntax.mlty = uu____7507;
             FStar_Extraction_ML_Syntax.loc = uu____7508;_},_rid::init1::[])
          when
          let uu____7517 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7517 = "FStar.HyperStack.ST.ralloc" ->
          let uu____7521 =
            let uu____7528 = translate_expr env init1  in
            (Eternal, uu____7528, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7521
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
             FStar_Extraction_ML_Syntax.loc = uu____7536;_},_e0::e1::e2::[])
          when
          ((let uu____7548 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7548 = "FStar.Buffer.rcreate") ||
             (let uu____7553 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7553 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7558 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7558 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7562 =
            let uu____7569 = translate_expr env e1  in
            let uu____7570 = translate_expr env e2  in
            (Eternal, uu____7569, uu____7570)  in
          EBufCreate uu____7562
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
             FStar_Extraction_ML_Syntax.loc = uu____7576;_},uu____7577)
          when
          (((((let uu____7588 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7588 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7593 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____7593 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7598 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7598 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7603 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7603 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7608 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7608 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7613 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7613 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7619;
                  FStar_Extraction_ML_Syntax.loc = uu____7620;_},uu____7621);
             FStar_Extraction_ML_Syntax.mlty = uu____7622;
             FStar_Extraction_ML_Syntax.loc = uu____7623;_},_erid::elen::[])
          when
          let uu____7632 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7632 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7636 =
            let uu____7641 = translate_expr env elen  in
            (Eternal, uu____7641)  in
          EBufCreateNoInit uu____7636
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7643;
                  FStar_Extraction_ML_Syntax.loc = uu____7644;_},uu____7645);
             FStar_Extraction_ML_Syntax.mlty = uu____7646;
             FStar_Extraction_ML_Syntax.loc = uu____7647;_},_rid::init1::[])
          when
          let uu____7656 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7656 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7660 =
            let uu____7667 = translate_expr env init1  in
            (ManuallyManaged, uu____7667, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7660
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7671;
                  FStar_Extraction_ML_Syntax.loc = uu____7672;_},uu____7673);
             FStar_Extraction_ML_Syntax.mlty = uu____7674;
             FStar_Extraction_ML_Syntax.loc = uu____7675;_},_e0::e1::e2::[])
          when
          (((let uu____7687 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7687 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7692 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7692 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7697 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7697 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7702 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7702 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7706 =
            let uu____7713 = translate_expr env e1  in
            let uu____7714 = translate_expr env e2  in
            (ManuallyManaged, uu____7713, uu____7714)  in
          EBufCreate uu____7706
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7716;
                  FStar_Extraction_ML_Syntax.loc = uu____7717;_},uu____7718);
             FStar_Extraction_ML_Syntax.mlty = uu____7719;
             FStar_Extraction_ML_Syntax.loc = uu____7720;_},_erid::elen::[])
          when
          let uu____7729 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7729 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7733 =
            let uu____7738 = translate_expr env elen  in
            (ManuallyManaged, uu____7738)  in
          EBufCreateNoInit uu____7733
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7740;
                  FStar_Extraction_ML_Syntax.loc = uu____7741;_},uu____7742);
             FStar_Extraction_ML_Syntax.mlty = uu____7743;
             FStar_Extraction_ML_Syntax.loc = uu____7744;_},e2::[])
          when
          let uu____7752 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7752 = "FStar.HyperStack.ST.rfree" ->
          let uu____7756 = translate_expr env e2  in EBufFree uu____7756
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7758;
                  FStar_Extraction_ML_Syntax.loc = uu____7759;_},uu____7760);
             FStar_Extraction_ML_Syntax.mlty = uu____7761;
             FStar_Extraction_ML_Syntax.loc = uu____7762;_},e2::[])
          when
          (let uu____7772 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7772 = "FStar.Buffer.rfree") ||
            (let uu____7777 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7777 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7781 = translate_expr env e2  in EBufFree uu____7781
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7783;
                  FStar_Extraction_ML_Syntax.loc = uu____7784;_},uu____7785);
             FStar_Extraction_ML_Syntax.mlty = uu____7786;
             FStar_Extraction_ML_Syntax.loc = uu____7787;_},e1::e2::_e3::[])
          when
          let uu____7797 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7797 = "FStar.Buffer.sub" ->
          let uu____7801 =
            let uu____7806 = translate_expr env e1  in
            let uu____7807 = translate_expr env e2  in
            (uu____7806, uu____7807)  in
          EBufSub uu____7801
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7809;
                  FStar_Extraction_ML_Syntax.loc = uu____7810;_},uu____7811);
             FStar_Extraction_ML_Syntax.mlty = uu____7812;
             FStar_Extraction_ML_Syntax.loc = uu____7813;_},e1::e2::_e3::[])
          when
          (let uu____7825 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7825 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7830 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7830 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7834 =
            let uu____7839 = translate_expr env e1  in
            let uu____7840 = translate_expr env e2  in
            (uu____7839, uu____7840)  in
          EBufSub uu____7834
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7842;
                  FStar_Extraction_ML_Syntax.loc = uu____7843;_},uu____7844);
             FStar_Extraction_ML_Syntax.mlty = uu____7845;
             FStar_Extraction_ML_Syntax.loc = uu____7846;_},e1::e2::[])
          when
          let uu____7855 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7855 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7860;
                  FStar_Extraction_ML_Syntax.loc = uu____7861;_},uu____7862);
             FStar_Extraction_ML_Syntax.mlty = uu____7863;
             FStar_Extraction_ML_Syntax.loc = uu____7864;_},e1::e2::[])
          when
          let uu____7873 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7873 = "FStar.Buffer.offset" ->
          let uu____7877 =
            let uu____7882 = translate_expr env e1  in
            let uu____7883 = translate_expr env e2  in
            (uu____7882, uu____7883)  in
          EBufSub uu____7877
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
             FStar_Extraction_ML_Syntax.loc = uu____7889;_},e1::e2::[])
          when
          let uu____7898 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7898 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7902 =
            let uu____7907 = translate_expr env e1  in
            let uu____7908 = translate_expr env e2  in
            (uu____7907, uu____7908)  in
          EBufSub uu____7902
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7910;
                  FStar_Extraction_ML_Syntax.loc = uu____7911;_},uu____7912);
             FStar_Extraction_ML_Syntax.mlty = uu____7913;
             FStar_Extraction_ML_Syntax.loc = uu____7914;_},e1::e2::e3::[])
          when
          (((let uu____7926 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7926 = "FStar.Buffer.upd") ||
              (let uu____7931 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7931 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7936 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7936 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7941 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7941 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7945 =
            let uu____7952 = translate_expr env e1  in
            let uu____7953 = translate_expr env e2  in
            let uu____7954 = translate_expr env e3  in
            (uu____7952, uu____7953, uu____7954)  in
          EBufWrite uu____7945
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7956;
                  FStar_Extraction_ML_Syntax.loc = uu____7957;_},uu____7958);
             FStar_Extraction_ML_Syntax.mlty = uu____7959;
             FStar_Extraction_ML_Syntax.loc = uu____7960;_},e1::e2::[])
          when
          let uu____7969 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7969 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7973 =
            let uu____7980 = translate_expr env e1  in
            let uu____7981 = translate_expr env e2  in
            (uu____7980, (EConstant (UInt32, "0")), uu____7981)  in
          EBufWrite uu____7973
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7985;
             FStar_Extraction_ML_Syntax.loc = uu____7986;_},uu____7987::[])
          when
          let uu____7990 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7990 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7995;
             FStar_Extraction_ML_Syntax.loc = uu____7996;_},uu____7997::[])
          when
          let uu____8000 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8000 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8005;
                  FStar_Extraction_ML_Syntax.loc = uu____8006;_},uu____8007);
             FStar_Extraction_ML_Syntax.mlty = uu____8008;
             FStar_Extraction_ML_Syntax.loc = uu____8009;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____8023 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____8023 = "FStar.Buffer.blit") ||
             (let uu____8028 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____8028 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____8033 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8033 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____8037 =
            let uu____8048 = translate_expr env e1  in
            let uu____8049 = translate_expr env e2  in
            let uu____8050 = translate_expr env e3  in
            let uu____8051 = translate_expr env e4  in
            let uu____8052 = translate_expr env e5  in
            (uu____8048, uu____8049, uu____8050, uu____8051, uu____8052)  in
          EBufBlit uu____8037
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8054;
                  FStar_Extraction_ML_Syntax.loc = uu____8055;_},uu____8056);
             FStar_Extraction_ML_Syntax.mlty = uu____8057;
             FStar_Extraction_ML_Syntax.loc = uu____8058;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____8074 =
            let uu____8081 = translate_expr env e1  in
            let uu____8082 = translate_expr env e2  in
            let uu____8083 = translate_expr env e3  in
            (uu____8081, uu____8082, uu____8083)  in
          EBufFill uu____8074
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____8085;
             FStar_Extraction_ML_Syntax.loc = uu____8086;_},uu____8087::[])
          when
          let uu____8090 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8090 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8095;
                  FStar_Extraction_ML_Syntax.loc = uu____8096;_},uu____8097);
             FStar_Extraction_ML_Syntax.mlty = uu____8098;
             FStar_Extraction_ML_Syntax.loc = uu____8099;_},_ebuf::_eseq::[])
          when
          (((let uu____8110 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8110 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____8115 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____8115 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____8120 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____8120 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____8125 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8125 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8130;
                  FStar_Extraction_ML_Syntax.loc = uu____8131;_},uu____8132);
             FStar_Extraction_ML_Syntax.mlty = uu____8133;
             FStar_Extraction_ML_Syntax.loc = uu____8134;_},e1::[])
          when
          ((((let uu____8144 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____8144 = "LowStar.ConstBuffer.of_buffer") ||
               (let uu____8149 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____8149 = "LowStar.ConstBuffer.of_ibuffer"))
              ||
              (let uu____8154 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____8154 = "LowStar.ConstBuffer.cast"))
             ||
             (let uu____8159 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____8159 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____8164 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8164 = "LowStar.ConstBuffer.to_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____8169;
             FStar_Extraction_ML_Syntax.loc = uu____8170;_},e1::[])
          when
          let uu____8174 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8174 = "Obj.repr" ->
          let uu____8178 =
            let uu____8183 = translate_expr env e1  in (uu____8183, TAny)  in
          ECast uu____8178
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____8186;
             FStar_Extraction_ML_Syntax.loc = uu____8187;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____8203 = FStar_Util.must (mk_width m)  in
          let uu____8204 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____8203 uu____8204 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____8206;
             FStar_Extraction_ML_Syntax.loc = uu____8207;_},args)
          when is_bool_op op ->
          let uu____8221 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____8221 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8223;
             FStar_Extraction_ML_Syntax.loc = uu____8224;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8226;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8227;_}::[])
          when is_machine_int m ->
          let uu____8252 =
            let uu____8258 = FStar_Util.must (mk_width m)  in (uu____8258, c)
             in
          EConstant uu____8252
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8261;
             FStar_Extraction_ML_Syntax.loc = uu____8262;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8264;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8265;_}::[])
          when is_machine_int m ->
          let uu____8290 =
            let uu____8296 = FStar_Util.must (mk_width m)  in (uu____8296, c)
             in
          EConstant uu____8290
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8298;
             FStar_Extraction_ML_Syntax.loc = uu____8299;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8301;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8302;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8315 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8317;
             FStar_Extraction_ML_Syntax.loc = uu____8318;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8320;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8321;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8338 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8340;
             FStar_Extraction_ML_Syntax.loc = uu____8341;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8343;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8344;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8359 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8361;
             FStar_Extraction_ML_Syntax.loc = uu____8362;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8364;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8365;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8380 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____8383;
             FStar_Extraction_ML_Syntax.loc = uu____8384;_},arg::[])
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
            let uu____8412 =
              let uu____8417 = translate_expr env arg  in
              (uu____8417, (TInt UInt64))  in
            ECast uu____8412
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8422 =
                 let uu____8427 = translate_expr env arg  in
                 (uu____8427, (TInt UInt32))  in
               ECast uu____8422)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8432 =
                   let uu____8437 = translate_expr env arg  in
                   (uu____8437, (TInt UInt16))  in
                 ECast uu____8432)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8442 =
                     let uu____8447 = translate_expr env arg  in
                     (uu____8447, (TInt UInt8))  in
                   ECast uu____8442)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8452 =
                       let uu____8457 = translate_expr env arg  in
                       (uu____8457, (TInt Int64))  in
                     ECast uu____8452)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8462 =
                         let uu____8467 = translate_expr env arg  in
                         (uu____8467, (TInt Int32))  in
                       ECast uu____8462)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8472 =
                           let uu____8477 = translate_expr env arg  in
                           (uu____8477, (TInt Int16))  in
                         ECast uu____8472)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8482 =
                             let uu____8487 = translate_expr env arg  in
                             (uu____8487, (TInt Int8))  in
                           ECast uu____8482)
                        else
                          (let uu____8490 =
                             let uu____8497 =
                               let uu____8500 = translate_expr env arg  in
                               [uu____8500]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8497)
                              in
                           EApp uu____8490)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8520 =
            let uu____8527 = translate_expr env head1  in
            let uu____8528 = FStar_List.map (translate_expr env) args  in
            (uu____8527, uu____8528)  in
          EApp uu____8520
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8539 =
            let uu____8546 = translate_expr env head1  in
            let uu____8547 = FStar_List.map (translate_type env) ty_args  in
            (uu____8546, uu____8547)  in
          ETypApp uu____8539
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8555 =
            let uu____8560 = translate_expr env e1  in
            let uu____8561 = translate_type env t_to  in
            (uu____8560, uu____8561)  in
          ECast uu____8555
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8562,fields) ->
          let uu____8584 =
            let uu____8596 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8597 =
              FStar_List.map
                (fun uu____8619  ->
                   match uu____8619 with
                   | (field,expr) ->
                       let uu____8634 = translate_expr env expr  in
                       (field, uu____8634)) fields
               in
            (uu____8596, uu____8597)  in
          EFlat uu____8584
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8645 =
            let uu____8653 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8654 = translate_expr env e1  in
            (uu____8653, uu____8654, (FStar_Pervasives_Native.snd path))  in
          EField uu____8645
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8660 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8673) ->
          let uu____8678 =
            let uu____8680 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8680
             in
          failwith uu____8678
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8692 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8692
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8698 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8698
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8701,cons1),es) ->
          let uu____8716 =
            let uu____8726 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8727 = FStar_List.map (translate_expr env) es  in
            (uu____8726, cons1, uu____8727)  in
          ECons uu____8716
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8753 =
            let uu____8762 = translate_expr env1 body  in
            let uu____8763 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8762, uu____8763)  in
          EFun uu____8753
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8773 =
            let uu____8780 = translate_expr env e1  in
            let uu____8781 = translate_expr env e2  in
            let uu____8782 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8780, uu____8781, uu____8782)  in
          EIfThenElse uu____8773
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8784 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8792 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8808 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8826 =
              let uu____8841 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8841)  in
            TApp uu____8826
          else TQualified lid
      | uu____8856 ->
          let uu____8857 =
            let uu____8859 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8859
             in
          failwith uu____8857

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
    fun uu____8893  ->
      match uu____8893 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8920 = translate_pat env pat  in
            (match uu____8920 with
             | (env1,pat1) ->
                 let uu____8931 = translate_expr env1 expr  in
                 (pat1, uu____8931))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8939  ->
    match uu___7_8939 with
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
          let uu____9006 =
            let uu____9007 =
              let uu____9013 = translate_width sw  in (uu____9013, s)  in
            PConstant uu____9007  in
          (env, uu____9006)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____9023,cons1),ps) ->
          let uu____9038 =
            FStar_List.fold_left
              (fun uu____9058  ->
                 fun p1  ->
                   match uu____9058 with
                   | (env1,acc) ->
                       let uu____9078 = translate_pat env1 p1  in
                       (match uu____9078 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____9038 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____9108,ps) ->
          let uu____9130 =
            FStar_List.fold_left
              (fun uu____9167  ->
                 fun uu____9168  ->
                   match (uu____9167, uu____9168) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____9248 = translate_pat env1 p1  in
                       (match uu____9248 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____9130 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____9319 =
            FStar_List.fold_left
              (fun uu____9339  ->
                 fun p1  ->
                   match uu____9339 with
                   | (env1,acc) ->
                       let uu____9359 = translate_pat env1 p1  in
                       (match uu____9359 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____9319 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9386 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9392 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9406 =
            let uu____9408 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____9408
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____9406
          then
            let uu____9423 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9423
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9450) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9468 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9470 ->
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
          let uu____9494 =
            let uu____9501 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9501)  in
          EApp uu____9494
