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
             | (uu____6402,name,_mangled_name,uu____6405,uu____6406,uu____6407)
                 ->
                 ((let uu____6423 =
                     let uu____6429 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6429)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6423);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6437 = find_t env name  in TBound uu____6437
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6440,t2) ->
          let uu____6442 =
            let uu____6447 = translate_type env t1  in
            let uu____6448 = translate_type env t2  in
            (uu____6447, uu____6448)  in
          TArrow uu____6442
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6452 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6452 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6459 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6459 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6476 = FStar_Util.must (mk_width m)  in TInt uu____6476
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6490 = FStar_Util.must (mk_width m)  in TInt uu____6490
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6495 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6495 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6499::arg::uu____6501::[],p) when
          (((let uu____6507 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6507 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6512 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6512 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6517 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6517 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6522 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6522 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6526 = translate_type env arg  in TBuf uu____6526
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6528::[],p) when
          ((((((((((let uu____6534 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6534 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6539 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6539 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6544 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6544 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6549 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6549 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6554 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6554 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6559 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6559 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6564 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6564 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6569 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6569 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6574 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6574 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6579 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6579 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6584 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6584 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6588 = translate_type env arg  in TBuf uu____6588
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6590::uu____6591::[],p) when
          let uu____6595 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6595 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6599 = translate_type env arg  in TBuf uu____6599
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6604 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6604 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6608 = translate_type env arg  in TBuf uu____6608
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6615 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6615 = "FStar.Buffer.buffer") ||
                        (let uu____6620 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6620 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6625 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6625 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6630 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6630 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6635 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6635 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6640 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6640 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6645 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6645 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6650 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6650 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6655 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6655 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6660 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6660 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6665 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6665 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6670 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6670 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6675 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6675 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6680 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6680 = "FStar.HyperStack.ST.mmref")
          -> let uu____6684 = translate_type env arg  in TBuf uu____6684
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6685::arg::[],p) when
          (let uu____6692 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6692 = "FStar.HyperStack.s_ref") ||
            (let uu____6697 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6697 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6701 = translate_type env arg  in TBuf uu____6701
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6702::[],p) when
          let uu____6706 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6706 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6758 = FStar_List.map (translate_type env) args  in
          TTuple uu____6758
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6769 =
              let uu____6784 = FStar_List.map (translate_type env) args  in
              (lid, uu____6784)  in
            TApp uu____6769
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6802 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6802

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
    fun uu____6820  ->
      match uu____6820 with
      | (name,typ) ->
          let uu____6830 = translate_type env typ  in
          { name; typ = uu____6830; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6837 = find env name  in EBound uu____6837
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6851 =
            let uu____6856 = FStar_Util.must (mk_op op)  in
            let uu____6857 = FStar_Util.must (mk_width m)  in
            (uu____6856, uu____6857)  in
          EOp uu____6851
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6867 =
            let uu____6872 = FStar_Util.must (mk_bool_op op)  in
            (uu____6872, Bool)  in
          EOp uu____6867
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
            let uu____6895 = translate_type env typ  in
            { name; typ = uu____6895; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6922 =
            let uu____6933 = translate_expr env expr  in
            let uu____6934 = translate_branches env branches  in
            (uu____6933, uu____6934)  in
          EMatch uu____6922
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6948;
                  FStar_Extraction_ML_Syntax.loc = uu____6949;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6951;
             FStar_Extraction_ML_Syntax.loc = uu____6952;_},arg::[])
          when
          let uu____6958 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6958 = "FStar.Dyn.undyn" ->
          let uu____6962 =
            let uu____6967 = translate_expr env arg  in
            let uu____6968 = translate_type env t  in
            (uu____6967, uu____6968)  in
          ECast uu____6962
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
             FStar_Extraction_ML_Syntax.loc = uu____6974;_},uu____6975)
          when
          let uu____6984 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6984 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6989;
                  FStar_Extraction_ML_Syntax.loc = uu____6990;_},uu____6991);
             FStar_Extraction_ML_Syntax.mlty = uu____6992;
             FStar_Extraction_ML_Syntax.loc = uu____6993;_},arg::[])
          when
          ((let uu____7003 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7003 = "FStar.HyperStack.All.failwith") ||
             (let uu____7008 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7008 = "FStar.Error.unexpected"))
            ||
            (let uu____7013 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7013 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____7018;
               FStar_Extraction_ML_Syntax.loc = uu____7019;_} -> EAbortS msg
           | uu____7021 ->
               let print7 =
                 let uu____7023 =
                   let uu____7024 =
                     let uu____7025 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____7025
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____7024  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____7023
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7032;
                  FStar_Extraction_ML_Syntax.loc = uu____7033;_},uu____7034);
             FStar_Extraction_ML_Syntax.mlty = uu____7035;
             FStar_Extraction_ML_Syntax.loc = uu____7036;_},e1::[])
          when
          (let uu____7046 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7046 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____7051 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7051 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7056;
                  FStar_Extraction_ML_Syntax.loc = uu____7057;_},uu____7058);
             FStar_Extraction_ML_Syntax.mlty = uu____7059;
             FStar_Extraction_ML_Syntax.loc = uu____7060;_},e1::e2::[])
          when
          ((((let uu____7071 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7071 = "FStar.Buffer.index") ||
               (let uu____7076 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7076 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____7081 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7081 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____7086 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7086 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____7091 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7091 = "LowStar.ConstBuffer.index")
          ->
          let uu____7095 =
            let uu____7100 = translate_expr env e1  in
            let uu____7101 = translate_expr env e2  in
            (uu____7100, uu____7101)  in
          EBufRead uu____7095
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7103;
                  FStar_Extraction_ML_Syntax.loc = uu____7104;_},uu____7105);
             FStar_Extraction_ML_Syntax.mlty = uu____7106;
             FStar_Extraction_ML_Syntax.loc = uu____7107;_},e1::[])
          when
          let uu____7115 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7115 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____7119 =
            let uu____7124 = translate_expr env e1  in
            (uu____7124, (EConstant (UInt32, "0")))  in
          EBufRead uu____7119
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
             FStar_Extraction_ML_Syntax.loc = uu____7132;_},e1::e2::[])
          when
          ((let uu____7143 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7143 = "FStar.Buffer.create") ||
             (let uu____7148 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7148 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7153 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7153 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7157 =
            let uu____7164 = translate_expr env e1  in
            let uu____7165 = translate_expr env e2  in
            (Stack, uu____7164, uu____7165)  in
          EBufCreate uu____7157
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7167;
                  FStar_Extraction_ML_Syntax.loc = uu____7168;_},uu____7169);
             FStar_Extraction_ML_Syntax.mlty = uu____7170;
             FStar_Extraction_ML_Syntax.loc = uu____7171;_},elen::[])
          when
          let uu____7179 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7179 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7183 =
            let uu____7188 = translate_expr env elen  in (Stack, uu____7188)
             in
          EBufCreateNoInit uu____7183
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7190;
                  FStar_Extraction_ML_Syntax.loc = uu____7191;_},uu____7192);
             FStar_Extraction_ML_Syntax.mlty = uu____7193;
             FStar_Extraction_ML_Syntax.loc = uu____7194;_},init1::[])
          when
          let uu____7202 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7202 = "FStar.HyperStack.ST.salloc" ->
          let uu____7206 =
            let uu____7213 = translate_expr env init1  in
            (Stack, uu____7213, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7206
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7217;
                  FStar_Extraction_ML_Syntax.loc = uu____7218;_},uu____7219);
             FStar_Extraction_ML_Syntax.mlty = uu____7220;
             FStar_Extraction_ML_Syntax.loc = uu____7221;_},e2::[])
          when
          ((let uu____7231 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7231 = "FStar.Buffer.createL") ||
             (let uu____7236 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7236 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7241 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7241 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7245 =
            let uu____7252 =
              let uu____7255 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7255  in
            (Stack, uu____7252)  in
          EBufCreateL uu____7245
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7261;
                  FStar_Extraction_ML_Syntax.loc = uu____7262;_},uu____7263);
             FStar_Extraction_ML_Syntax.mlty = uu____7264;
             FStar_Extraction_ML_Syntax.loc = uu____7265;_},_erid::e2::[])
          when
          (let uu____7276 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7276 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7281 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7281 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7285 =
            let uu____7292 =
              let uu____7295 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7295  in
            (Eternal, uu____7292)  in
          EBufCreateL uu____7285
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7301;
                  FStar_Extraction_ML_Syntax.loc = uu____7302;_},uu____7303);
             FStar_Extraction_ML_Syntax.mlty = uu____7304;
             FStar_Extraction_ML_Syntax.loc = uu____7305;_},_rid::init1::[])
          when
          let uu____7314 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7314 = "FStar.HyperStack.ST.ralloc" ->
          let uu____7318 =
            let uu____7325 = translate_expr env init1  in
            (Eternal, uu____7325, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7318
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7329;
                  FStar_Extraction_ML_Syntax.loc = uu____7330;_},uu____7331);
             FStar_Extraction_ML_Syntax.mlty = uu____7332;
             FStar_Extraction_ML_Syntax.loc = uu____7333;_},_e0::e1::e2::[])
          when
          ((let uu____7345 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7345 = "FStar.Buffer.rcreate") ||
             (let uu____7350 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7350 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7355 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7355 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7359 =
            let uu____7366 = translate_expr env e1  in
            let uu____7367 = translate_expr env e2  in
            (Eternal, uu____7366, uu____7367)  in
          EBufCreate uu____7359
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7369;
                  FStar_Extraction_ML_Syntax.loc = uu____7370;_},uu____7371);
             FStar_Extraction_ML_Syntax.mlty = uu____7372;
             FStar_Extraction_ML_Syntax.loc = uu____7373;_},uu____7374)
          when
          (((((let uu____7385 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7385 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7390 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____7390 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7395 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7395 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7400 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7400 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7405 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7405 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7410 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7410 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7416;
                  FStar_Extraction_ML_Syntax.loc = uu____7417;_},uu____7418);
             FStar_Extraction_ML_Syntax.mlty = uu____7419;
             FStar_Extraction_ML_Syntax.loc = uu____7420;_},_erid::elen::[])
          when
          let uu____7429 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7429 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7433 =
            let uu____7438 = translate_expr env elen  in
            (Eternal, uu____7438)  in
          EBufCreateNoInit uu____7433
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7440;
                  FStar_Extraction_ML_Syntax.loc = uu____7441;_},uu____7442);
             FStar_Extraction_ML_Syntax.mlty = uu____7443;
             FStar_Extraction_ML_Syntax.loc = uu____7444;_},_rid::init1::[])
          when
          let uu____7453 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7453 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7457 =
            let uu____7464 = translate_expr env init1  in
            (ManuallyManaged, uu____7464, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7457
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7468;
                  FStar_Extraction_ML_Syntax.loc = uu____7469;_},uu____7470);
             FStar_Extraction_ML_Syntax.mlty = uu____7471;
             FStar_Extraction_ML_Syntax.loc = uu____7472;_},_e0::e1::e2::[])
          when
          (((let uu____7484 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7484 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7489 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7489 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7494 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7494 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7499 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7499 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7503 =
            let uu____7510 = translate_expr env e1  in
            let uu____7511 = translate_expr env e2  in
            (ManuallyManaged, uu____7510, uu____7511)  in
          EBufCreate uu____7503
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7513;
                  FStar_Extraction_ML_Syntax.loc = uu____7514;_},uu____7515);
             FStar_Extraction_ML_Syntax.mlty = uu____7516;
             FStar_Extraction_ML_Syntax.loc = uu____7517;_},_erid::elen::[])
          when
          let uu____7526 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7526 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7530 =
            let uu____7535 = translate_expr env elen  in
            (ManuallyManaged, uu____7535)  in
          EBufCreateNoInit uu____7530
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7537;
                  FStar_Extraction_ML_Syntax.loc = uu____7538;_},uu____7539);
             FStar_Extraction_ML_Syntax.mlty = uu____7540;
             FStar_Extraction_ML_Syntax.loc = uu____7541;_},e2::[])
          when
          let uu____7549 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7549 = "FStar.HyperStack.ST.rfree" ->
          let uu____7553 = translate_expr env e2  in EBufFree uu____7553
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7555;
                  FStar_Extraction_ML_Syntax.loc = uu____7556;_},uu____7557);
             FStar_Extraction_ML_Syntax.mlty = uu____7558;
             FStar_Extraction_ML_Syntax.loc = uu____7559;_},e2::[])
          when
          (let uu____7569 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7569 = "FStar.Buffer.rfree") ||
            (let uu____7574 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7574 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7578 = translate_expr env e2  in EBufFree uu____7578
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
             FStar_Extraction_ML_Syntax.loc = uu____7584;_},e1::e2::_e3::[])
          when
          let uu____7594 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7594 = "FStar.Buffer.sub" ->
          let uu____7598 =
            let uu____7603 = translate_expr env e1  in
            let uu____7604 = translate_expr env e2  in
            (uu____7603, uu____7604)  in
          EBufSub uu____7598
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7606;
                  FStar_Extraction_ML_Syntax.loc = uu____7607;_},uu____7608);
             FStar_Extraction_ML_Syntax.mlty = uu____7609;
             FStar_Extraction_ML_Syntax.loc = uu____7610;_},e1::e2::_e3::[])
          when
          (let uu____7622 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7622 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7627 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7627 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7631 =
            let uu____7636 = translate_expr env e1  in
            let uu____7637 = translate_expr env e2  in
            (uu____7636, uu____7637)  in
          EBufSub uu____7631
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7639;
                  FStar_Extraction_ML_Syntax.loc = uu____7640;_},uu____7641);
             FStar_Extraction_ML_Syntax.mlty = uu____7642;
             FStar_Extraction_ML_Syntax.loc = uu____7643;_},e1::e2::[])
          when
          let uu____7652 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7652 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7657;
                  FStar_Extraction_ML_Syntax.loc = uu____7658;_},uu____7659);
             FStar_Extraction_ML_Syntax.mlty = uu____7660;
             FStar_Extraction_ML_Syntax.loc = uu____7661;_},e1::e2::[])
          when
          let uu____7670 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7670 = "FStar.Buffer.offset" ->
          let uu____7674 =
            let uu____7679 = translate_expr env e1  in
            let uu____7680 = translate_expr env e2  in
            (uu____7679, uu____7680)  in
          EBufSub uu____7674
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7682;
                  FStar_Extraction_ML_Syntax.loc = uu____7683;_},uu____7684);
             FStar_Extraction_ML_Syntax.mlty = uu____7685;
             FStar_Extraction_ML_Syntax.loc = uu____7686;_},e1::e2::[])
          when
          let uu____7695 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7695 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7699 =
            let uu____7704 = translate_expr env e1  in
            let uu____7705 = translate_expr env e2  in
            (uu____7704, uu____7705)  in
          EBufSub uu____7699
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7707;
                  FStar_Extraction_ML_Syntax.loc = uu____7708;_},uu____7709);
             FStar_Extraction_ML_Syntax.mlty = uu____7710;
             FStar_Extraction_ML_Syntax.loc = uu____7711;_},e1::e2::e3::[])
          when
          (((let uu____7723 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7723 = "FStar.Buffer.upd") ||
              (let uu____7728 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7728 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7733 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7733 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7738 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7738 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7742 =
            let uu____7749 = translate_expr env e1  in
            let uu____7750 = translate_expr env e2  in
            let uu____7751 = translate_expr env e3  in
            (uu____7749, uu____7750, uu____7751)  in
          EBufWrite uu____7742
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7753;
                  FStar_Extraction_ML_Syntax.loc = uu____7754;_},uu____7755);
             FStar_Extraction_ML_Syntax.mlty = uu____7756;
             FStar_Extraction_ML_Syntax.loc = uu____7757;_},e1::e2::[])
          when
          let uu____7766 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7766 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7770 =
            let uu____7777 = translate_expr env e1  in
            let uu____7778 = translate_expr env e2  in
            (uu____7777, (EConstant (UInt32, "0")), uu____7778)  in
          EBufWrite uu____7770
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7782;
             FStar_Extraction_ML_Syntax.loc = uu____7783;_},uu____7784::[])
          when
          let uu____7787 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7787 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7792;
             FStar_Extraction_ML_Syntax.loc = uu____7793;_},uu____7794::[])
          when
          let uu____7797 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7797 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7802;
                  FStar_Extraction_ML_Syntax.loc = uu____7803;_},uu____7804);
             FStar_Extraction_ML_Syntax.mlty = uu____7805;
             FStar_Extraction_ML_Syntax.loc = uu____7806;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7820 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7820 = "FStar.Buffer.blit") ||
             (let uu____7825 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7825 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7830 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7830 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7834 =
            let uu____7845 = translate_expr env e1  in
            let uu____7846 = translate_expr env e2  in
            let uu____7847 = translate_expr env e3  in
            let uu____7848 = translate_expr env e4  in
            let uu____7849 = translate_expr env e5  in
            (uu____7845, uu____7846, uu____7847, uu____7848, uu____7849)  in
          EBufBlit uu____7834
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7851;
                  FStar_Extraction_ML_Syntax.loc = uu____7852;_},uu____7853);
             FStar_Extraction_ML_Syntax.mlty = uu____7854;
             FStar_Extraction_ML_Syntax.loc = uu____7855;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7871 =
            let uu____7878 = translate_expr env e1  in
            let uu____7879 = translate_expr env e2  in
            let uu____7880 = translate_expr env e3  in
            (uu____7878, uu____7879, uu____7880)  in
          EBufFill uu____7871
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7882;
             FStar_Extraction_ML_Syntax.loc = uu____7883;_},uu____7884::[])
          when
          let uu____7887 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7887 = "FStar.HyperStack.ST.get" -> EUnit
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
             FStar_Extraction_ML_Syntax.loc = uu____7896;_},_ebuf::_eseq::[])
          when
          (((let uu____7907 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7907 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7912 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7912 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7917 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7917 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7922 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7922 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7927;
                  FStar_Extraction_ML_Syntax.loc = uu____7928;_},uu____7929);
             FStar_Extraction_ML_Syntax.mlty = uu____7930;
             FStar_Extraction_ML_Syntax.loc = uu____7931;_},e1::[])
          when
          ((((let uu____7941 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7941 = "LowStar.ConstBuffer.of_buffer") ||
               (let uu____7946 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7946 = "LowStar.ConstBuffer.of_ibuffer"))
              ||
              (let uu____7951 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7951 = "LowStar.ConstBuffer.cast"))
             ||
             (let uu____7956 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7956 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7961 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7961 = "LowStar.ConstBuffer.to_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7966;
             FStar_Extraction_ML_Syntax.loc = uu____7967;_},e1::[])
          when
          let uu____7971 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7971 = "Obj.repr" ->
          let uu____7975 =
            let uu____7980 = translate_expr env e1  in (uu____7980, TAny)  in
          ECast uu____7975
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7983;
             FStar_Extraction_ML_Syntax.loc = uu____7984;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____8000 = FStar_Util.must (mk_width m)  in
          let uu____8001 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____8000 uu____8001 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____8003;
             FStar_Extraction_ML_Syntax.loc = uu____8004;_},args)
          when is_bool_op op ->
          let uu____8018 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____8018 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8020;
             FStar_Extraction_ML_Syntax.loc = uu____8021;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8023;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8024;_}::[])
          when is_machine_int m ->
          let uu____8049 =
            let uu____8055 = FStar_Util.must (mk_width m)  in (uu____8055, c)
             in
          EConstant uu____8049
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8058;
             FStar_Extraction_ML_Syntax.loc = uu____8059;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8061;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8062;_}::[])
          when is_machine_int m ->
          let uu____8087 =
            let uu____8093 = FStar_Util.must (mk_width m)  in (uu____8093, c)
             in
          EConstant uu____8087
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8095;
             FStar_Extraction_ML_Syntax.loc = uu____8096;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8098;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8099;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8112 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8114;
             FStar_Extraction_ML_Syntax.loc = uu____8115;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8117;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8118;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8135 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8137;
             FStar_Extraction_ML_Syntax.loc = uu____8138;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8140;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8141;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8156 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8158;
             FStar_Extraction_ML_Syntax.loc = uu____8159;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8161;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8162;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8177 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____8180;
             FStar_Extraction_ML_Syntax.loc = uu____8181;_},arg::[])
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
            let uu____8209 =
              let uu____8214 = translate_expr env arg  in
              (uu____8214, (TInt UInt64))  in
            ECast uu____8209
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8219 =
                 let uu____8224 = translate_expr env arg  in
                 (uu____8224, (TInt UInt32))  in
               ECast uu____8219)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8229 =
                   let uu____8234 = translate_expr env arg  in
                   (uu____8234, (TInt UInt16))  in
                 ECast uu____8229)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8239 =
                     let uu____8244 = translate_expr env arg  in
                     (uu____8244, (TInt UInt8))  in
                   ECast uu____8239)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8249 =
                       let uu____8254 = translate_expr env arg  in
                       (uu____8254, (TInt Int64))  in
                     ECast uu____8249)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8259 =
                         let uu____8264 = translate_expr env arg  in
                         (uu____8264, (TInt Int32))  in
                       ECast uu____8259)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8269 =
                           let uu____8274 = translate_expr env arg  in
                           (uu____8274, (TInt Int16))  in
                         ECast uu____8269)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8279 =
                             let uu____8284 = translate_expr env arg  in
                             (uu____8284, (TInt Int8))  in
                           ECast uu____8279)
                        else
                          (let uu____8287 =
                             let uu____8294 =
                               let uu____8297 = translate_expr env arg  in
                               [uu____8297]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8294)
                              in
                           EApp uu____8287)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8317 =
            let uu____8324 = translate_expr env head1  in
            let uu____8325 = FStar_List.map (translate_expr env) args  in
            (uu____8324, uu____8325)  in
          EApp uu____8317
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8336 =
            let uu____8343 = translate_expr env head1  in
            let uu____8344 = FStar_List.map (translate_type env) ty_args  in
            (uu____8343, uu____8344)  in
          ETypApp uu____8336
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8352 =
            let uu____8357 = translate_expr env e1  in
            let uu____8358 = translate_type env t_to  in
            (uu____8357, uu____8358)  in
          ECast uu____8352
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8359,fields) ->
          let uu____8381 =
            let uu____8393 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8394 =
              FStar_List.map
                (fun uu____8416  ->
                   match uu____8416 with
                   | (field,expr) ->
                       let uu____8431 = translate_expr env expr  in
                       (field, uu____8431)) fields
               in
            (uu____8393, uu____8394)  in
          EFlat uu____8381
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8442 =
            let uu____8450 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8451 = translate_expr env e1  in
            (uu____8450, uu____8451, (FStar_Pervasives_Native.snd path))  in
          EField uu____8442
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8457 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8470) ->
          let uu____8475 =
            let uu____8477 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8477
             in
          failwith uu____8475
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8489 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8489
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8495 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8495
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8498,cons1),es) ->
          let uu____8513 =
            let uu____8523 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8524 = FStar_List.map (translate_expr env) es  in
            (uu____8523, cons1, uu____8524)  in
          ECons uu____8513
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8550 =
            let uu____8559 = translate_expr env1 body  in
            let uu____8560 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8559, uu____8560)  in
          EFun uu____8550
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8570 =
            let uu____8577 = translate_expr env e1  in
            let uu____8578 = translate_expr env e2  in
            let uu____8579 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8577, uu____8578, uu____8579)  in
          EIfThenElse uu____8570
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8581 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8589 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8605 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8623 =
              let uu____8638 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8638)  in
            TApp uu____8623
          else TQualified lid
      | uu____8653 ->
          let uu____8654 =
            let uu____8656 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8656
             in
          failwith uu____8654

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
    fun uu____8690  ->
      match uu____8690 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8717 = translate_pat env pat  in
            (match uu____8717 with
             | (env1,pat1) ->
                 let uu____8728 = translate_expr env1 expr  in
                 (pat1, uu____8728))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8736  ->
    match uu___7_8736 with
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
          let uu____8803 =
            let uu____8804 =
              let uu____8810 = translate_width sw  in (uu____8810, s)  in
            PConstant uu____8804  in
          (env, uu____8803)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8820,cons1),ps) ->
          let uu____8835 =
            FStar_List.fold_left
              (fun uu____8855  ->
                 fun p1  ->
                   match uu____8855 with
                   | (env1,acc) ->
                       let uu____8875 = translate_pat env1 p1  in
                       (match uu____8875 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8835 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8905,ps) ->
          let uu____8927 =
            FStar_List.fold_left
              (fun uu____8964  ->
                 fun uu____8965  ->
                   match (uu____8964, uu____8965) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____9045 = translate_pat env1 p1  in
                       (match uu____9045 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8927 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____9116 =
            FStar_List.fold_left
              (fun uu____9136  ->
                 fun p1  ->
                   match uu____9136 with
                   | (env1,acc) ->
                       let uu____9156 = translate_pat env1 p1  in
                       (match uu____9156 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____9116 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9183 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9189 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9203 =
            let uu____9205 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____9205
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____9203
          then
            let uu____9220 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9220
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9247) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9265 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9267 ->
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
          let uu____9291 =
            let uu____9298 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9298)  in
          EApp uu____9291
