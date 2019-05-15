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
    match projectee with | DGlobal _0 -> true | uu____732 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____843 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____968 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1075 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1207 -> false
  
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee  ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
  
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1324 -> false
  
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
    | uu____1465 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1533 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1626 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1637 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1648 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1659 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1670 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1681 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1692 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1703 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1716 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1737 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1750 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1773 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1796 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1817 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1828 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1839 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1850 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1861 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1872 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1885 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1915 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1963 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1996 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____2014 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____2057 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____2100 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____2143 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2182 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2211 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2248 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2289 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2326 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2367 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2408 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2467 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2520 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2555 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2585 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2596 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2609 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2630 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2641 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2653 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2683 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2742 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2786 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2823 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2862 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2896 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2948 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2986 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____3016 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____3060 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____3082 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____3105 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3135 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3146 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3157 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3168 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3179 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3190 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3201 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3212 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3223 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3234 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3245 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3256 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3267 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3278 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3289 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3300 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3311 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3322 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3333 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3344 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3355 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3366 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3377 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3388 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3399 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3410 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3423 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3445 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3471 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3513 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3545 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3590 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3623 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3634 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3645 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3656 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3667 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3678 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3689 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3700 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3711 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3722 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3771 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3790 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3808 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3828 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____3870 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____3881 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____3897 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____3929 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____3965 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____4028 -> false
  
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
  'Auu____4129 'Auu____4130 'Auu____4131 .
    ('Auu____4129 * 'Auu____4130 * 'Auu____4131) -> 'Auu____4129
  = fun uu____4142  -> match uu____4142 with | (x,uu____4150,uu____4151) -> x 
let snd3 :
  'Auu____4161 'Auu____4162 'Auu____4163 .
    ('Auu____4161 * 'Auu____4162 * 'Auu____4163) -> 'Auu____4162
  = fun uu____4174  -> match uu____4174 with | (uu____4181,x,uu____4183) -> x 
let thd3 :
  'Auu____4193 'Auu____4194 'Auu____4195 .
    ('Auu____4193 * 'Auu____4194 * 'Auu____4195) -> 'Auu____4195
  = fun uu____4206  -> match uu____4206 with | (uu____4213,uu____4214,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4224  ->
    match uu___0_4224 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4236 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4246  ->
    match uu___1_4246 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4255 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4276  ->
    match uu___2_4276 with
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
    | uu____4321 -> FStar_Pervasives_Native.None
  
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
      let uu___163_4477 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___163_4477.names_t);
        module_name = (uu___163_4477.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___167_4491 = env  in
      {
        names = (uu___167_4491.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___167_4491.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4506 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4506 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___178_4530  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___177_4537 ->
          let uu____4539 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4539
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___187_4559  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___186_4568 ->
          let uu____4570 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4570
  
let add_binders :
  'Auu____4581 . env -> (Prims.string * 'Auu____4581) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4616  ->
             match uu____4616 with | (name,uu____4623) -> extend env1 name)
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
      | uu____4675 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____4894  ->
    match uu____4894 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____4943 = m  in
               match uu____4943 with
               | (path,uu____4958,uu____4959) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___229_4977  ->
                  match () with
                  | () ->
                      ((let uu____4981 =
                          let uu____4983 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____4983  in
                        if uu____4981
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____4989 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____4989))) ()
             with
             | e ->
                 ((let uu____4998 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____4998);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____5001  ->
    match uu____5001 with
    | (module_name,modul,uu____5016) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5051 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5065  ->
         match uu___3_5065 with
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
         | uu____5076 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5080 =
      FStar_List.choose
        (fun uu___4_5087  ->
           match uu___4_5087 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5094 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5080 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5107 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5121 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5123 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5128) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5155;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5158;_} when
            FStar_Util.for_some
              (fun uu___5_5163  ->
                 match uu___5_5163 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5166 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5189) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5211 -> []  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____5219 =
                let uu____5220 =
                  let uu____5246 = translate_cc meta  in
                  let uu____5249 = translate_flags meta  in
                  let uu____5252 = translate_type env t0  in
                  (uu____5246, uu____5249, name1, uu____5252, arg_names)  in
                DExternal uu____5220  in
              FStar_Pervasives_Native.Some uu____5219
            else
              ((let uu____5271 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5271);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5277;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5280;
                FStar_Extraction_ML_Syntax.loc = uu____5281;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5283;_} ->
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
               let rec find_return_type eff i uu___6_5340 =
                 match uu___6_5340 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5349,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5369 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5369 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5395 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5395 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5413) ->
                           let uu____5414 = translate_flags meta  in
                           MustDisappear :: uu____5414
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5417 = translate_flags meta  in
                           MustDisappear :: uu____5417
                       | uu____5420 -> translate_flags meta  in
                     try
                       (fun uu___375_5429  ->
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
                         ((let uu____5461 =
                             let uu____5467 =
                               let uu____5469 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5469 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5467)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5461);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5495;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5498;_} ->
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
                 (fun uu___402_5535  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5559 =
                       let uu____5565 =
                         let uu____5567 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5569 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5567
                           uu____5569
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5565)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5559);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5587;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5588;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5589;
            FStar_Extraction_ML_Syntax.print_typ = uu____5590;_} ->
            ((let uu____5597 =
                let uu____5603 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5603)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5597);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5610 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5610
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5624 = ty  in
      match uu____5624 with
      | (uu____5627,uu____5628,uu____5629,uu____5630,flags,uu____5632) ->
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
                     (let uu____5706 =
                        let uu____5707 =
                          let uu____5727 = translate_flags flags1  in
                          let uu____5730 = translate_type env1 t  in
                          (name1, uu____5727, (FStar_List.length args),
                            uu____5730)
                           in
                        DTypeAlias uu____5707  in
                      FStar_Pervasives_Native.Some uu____5706)
             | (uu____5743,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5788 =
                   let uu____5789 =
                     let uu____5821 = translate_flags flags1  in
                     let uu____5824 =
                       FStar_List.map
                         (fun uu____5856  ->
                            match uu____5856 with
                            | (f,t) ->
                                let uu____5876 =
                                  let uu____5882 = translate_type env1 t  in
                                  (uu____5882, false)  in
                                (f, uu____5876)) fields
                        in
                     (name1, uu____5821, (FStar_List.length args),
                       uu____5824)
                      in
                   DTypeFlat uu____5789  in
                 FStar_Pervasives_Native.Some uu____5788
             | (uu____5915,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____5965 =
                   let uu____5966 =
                     let uu____6005 =
                       FStar_List.map
                         (fun uu____6058  ->
                            match uu____6058 with
                            | (cons1,ts) ->
                                let uu____6106 =
                                  FStar_List.map
                                    (fun uu____6138  ->
                                       match uu____6138 with
                                       | (name2,t) ->
                                           let uu____6158 =
                                             let uu____6164 =
                                               translate_type env1 t  in
                                             (uu____6164, false)  in
                                           (name2, uu____6158)) ts
                                   in
                                (cons1, uu____6106)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____6005)
                      in
                   DTypeVariant uu____5966  in
                 FStar_Pervasives_Native.Some uu____5965
             | (uu____6217,name,_mangled_name,uu____6220,uu____6221,uu____6222)
                 ->
                 ((let uu____6238 =
                     let uu____6244 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6244)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6238);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6252 = find_t env name  in TBound uu____6252
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6255,t2) ->
          let uu____6257 =
            let uu____6262 = translate_type env t1  in
            let uu____6263 = translate_type env t2  in
            (uu____6262, uu____6263)  in
          TArrow uu____6257
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6267 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6267 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6274 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6274 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6291 = FStar_Util.must (mk_width m)  in TInt uu____6291
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6305 = FStar_Util.must (mk_width m)  in TInt uu____6305
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6310 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6310 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6314::arg::uu____6316::[],p) when
          (((let uu____6322 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6322 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6327 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6327 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6332 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6332 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6337 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6337 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6341 = translate_type env arg  in TBuf uu____6341
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6343::[],p) when
          ((((((((((let uu____6349 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6349 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6354 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6354 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6359 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6359 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6364 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6364 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6369 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6369 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6374 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6374 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6379 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6379 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6384 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6384 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6389 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6389 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6394 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6394 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6399 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6399 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6403 = translate_type env arg  in TBuf uu____6403
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6405::uu____6406::[],p) when
          let uu____6410 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6410 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6414 = translate_type env arg  in TBuf uu____6414
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6421 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6421 = "FStar.Buffer.buffer") ||
                        (let uu____6426 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6426 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6431 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6431 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6436 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6436 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6441 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6441 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6446 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6446 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6451 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6451 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6456 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6456 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6461 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6461 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6466 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6466 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6471 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6471 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6476 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6476 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6481 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6481 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6486 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6486 = "FStar.HyperStack.ST.mmref")
          -> let uu____6490 = translate_type env arg  in TBuf uu____6490
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6491::arg::[],p) when
          (let uu____6498 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6498 = "FStar.HyperStack.s_ref") ||
            (let uu____6503 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6503 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6507 = translate_type env arg  in TBuf uu____6507
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6508::[],p) when
          let uu____6512 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6512 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6564 = FStar_List.map (translate_type env) args  in
          TTuple uu____6564
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____6575 =
              let uu____6590 = FStar_List.map (translate_type env) args  in
              (lid, uu____6590)  in
            TApp uu____6575
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6608 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6608

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
    fun uu____6626  ->
      match uu____6626 with
      | (name,typ) ->
          let uu____6636 = translate_type env typ  in
          { name; typ = uu____6636; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6643 = find env name  in EBound uu____6643
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6657 =
            let uu____6662 = FStar_Util.must (mk_op op)  in
            let uu____6663 = FStar_Util.must (mk_width m)  in
            (uu____6662, uu____6663)  in
          EOp uu____6657
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6673 =
            let uu____6678 = FStar_Util.must (mk_bool_op op)  in
            (uu____6678, Bool)  in
          EOp uu____6673
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
            let uu____6701 = translate_type env typ  in
            { name; typ = uu____6701; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6728 =
            let uu____6739 = translate_expr env expr  in
            let uu____6740 = translate_branches env branches  in
            (uu____6739, uu____6740)  in
          EMatch uu____6728
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6754;
                  FStar_Extraction_ML_Syntax.loc = uu____6755;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6757;
             FStar_Extraction_ML_Syntax.loc = uu____6758;_},arg::[])
          when
          let uu____6764 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6764 = "FStar.Dyn.undyn" ->
          let uu____6768 =
            let uu____6773 = translate_expr env arg  in
            let uu____6774 = translate_type env t  in
            (uu____6773, uu____6774)  in
          ECast uu____6768
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6776;
                  FStar_Extraction_ML_Syntax.loc = uu____6777;_},uu____6778);
             FStar_Extraction_ML_Syntax.mlty = uu____6779;
             FStar_Extraction_ML_Syntax.loc = uu____6780;_},uu____6781)
          when
          let uu____6790 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6790 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6795;
                  FStar_Extraction_ML_Syntax.loc = uu____6796;_},uu____6797);
             FStar_Extraction_ML_Syntax.mlty = uu____6798;
             FStar_Extraction_ML_Syntax.loc = uu____6799;_},arg::[])
          when
          ((let uu____6809 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6809 = "FStar.HyperStack.All.failwith") ||
             (let uu____6814 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6814 = "FStar.Error.unexpected"))
            ||
            (let uu____6819 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6819 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6824;
               FStar_Extraction_ML_Syntax.loc = uu____6825;_} -> EAbortS msg
           | uu____6827 ->
               let print7 =
                 let uu____6829 =
                   let uu____6830 =
                     let uu____6831 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6831
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6830  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6829
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6838;
                  FStar_Extraction_ML_Syntax.loc = uu____6839;_},uu____6840);
             FStar_Extraction_ML_Syntax.mlty = uu____6841;
             FStar_Extraction_ML_Syntax.loc = uu____6842;_},e1::[])
          when
          (let uu____6852 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6852 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6857 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6857 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6862;
                  FStar_Extraction_ML_Syntax.loc = uu____6863;_},uu____6864);
             FStar_Extraction_ML_Syntax.mlty = uu____6865;
             FStar_Extraction_ML_Syntax.loc = uu____6866;_},e1::e2::[])
          when
          (((let uu____6877 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6877 = "FStar.Buffer.index") ||
              (let uu____6882 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6882 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____6887 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6887 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____6892 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6892 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____6896 =
            let uu____6901 = translate_expr env e1  in
            let uu____6902 = translate_expr env e2  in
            (uu____6901, uu____6902)  in
          EBufRead uu____6896
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6904;
                  FStar_Extraction_ML_Syntax.loc = uu____6905;_},uu____6906);
             FStar_Extraction_ML_Syntax.mlty = uu____6907;
             FStar_Extraction_ML_Syntax.loc = uu____6908;_},e1::[])
          when
          let uu____6916 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6916 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6920 =
            let uu____6925 = translate_expr env e1  in
            (uu____6925, (EConstant (UInt32, "0")))  in
          EBufRead uu____6920
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6929;
                  FStar_Extraction_ML_Syntax.loc = uu____6930;_},uu____6931);
             FStar_Extraction_ML_Syntax.mlty = uu____6932;
             FStar_Extraction_ML_Syntax.loc = uu____6933;_},e1::e2::[])
          when
          ((let uu____6944 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6944 = "FStar.Buffer.create") ||
             (let uu____6949 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6949 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____6954 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6954 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____6958 =
            let uu____6965 = translate_expr env e1  in
            let uu____6966 = translate_expr env e2  in
            (Stack, uu____6965, uu____6966)  in
          EBufCreate uu____6958
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6968;
                  FStar_Extraction_ML_Syntax.loc = uu____6969;_},uu____6970);
             FStar_Extraction_ML_Syntax.mlty = uu____6971;
             FStar_Extraction_ML_Syntax.loc = uu____6972;_},elen::[])
          when
          let uu____6980 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6980 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____6984 =
            let uu____6989 = translate_expr env elen  in (Stack, uu____6989)
             in
          EBufCreateNoInit uu____6984
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6991;
                  FStar_Extraction_ML_Syntax.loc = uu____6992;_},uu____6993);
             FStar_Extraction_ML_Syntax.mlty = uu____6994;
             FStar_Extraction_ML_Syntax.loc = uu____6995;_},init1::[])
          when
          let uu____7003 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7003 = "FStar.HyperStack.ST.salloc" ->
          let uu____7007 =
            let uu____7014 = translate_expr env init1  in
            (Stack, uu____7014, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7007
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7018;
                  FStar_Extraction_ML_Syntax.loc = uu____7019;_},uu____7020);
             FStar_Extraction_ML_Syntax.mlty = uu____7021;
             FStar_Extraction_ML_Syntax.loc = uu____7022;_},e2::[])
          when
          ((let uu____7032 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7032 = "FStar.Buffer.createL") ||
             (let uu____7037 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7037 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7042 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7042 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7046 =
            let uu____7053 =
              let uu____7056 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7056  in
            (Stack, uu____7053)  in
          EBufCreateL uu____7046
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7062;
                  FStar_Extraction_ML_Syntax.loc = uu____7063;_},uu____7064);
             FStar_Extraction_ML_Syntax.mlty = uu____7065;
             FStar_Extraction_ML_Syntax.loc = uu____7066;_},_erid::e2::[])
          when
          (let uu____7077 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7077 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7082 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7082 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7086 =
            let uu____7093 =
              let uu____7096 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7096  in
            (Eternal, uu____7093)  in
          EBufCreateL uu____7086
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
             FStar_Extraction_ML_Syntax.loc = uu____7106;_},_rid::init1::[])
          when
          let uu____7115 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7115 = "FStar.HyperStack.ST.ralloc" ->
          let uu____7119 =
            let uu____7126 = translate_expr env init1  in
            (Eternal, uu____7126, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7119
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7130;
                  FStar_Extraction_ML_Syntax.loc = uu____7131;_},uu____7132);
             FStar_Extraction_ML_Syntax.mlty = uu____7133;
             FStar_Extraction_ML_Syntax.loc = uu____7134;_},_e0::e1::e2::[])
          when
          ((let uu____7146 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7146 = "FStar.Buffer.rcreate") ||
             (let uu____7151 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7151 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7156 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7156 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7160 =
            let uu____7167 = translate_expr env e1  in
            let uu____7168 = translate_expr env e2  in
            (Eternal, uu____7167, uu____7168)  in
          EBufCreate uu____7160
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
             FStar_Extraction_ML_Syntax.loc = uu____7174;_},_erid::elen::[])
          when
          let uu____7183 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7183 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7187 =
            let uu____7192 = translate_expr env elen  in
            (Eternal, uu____7192)  in
          EBufCreateNoInit uu____7187
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7194;
                  FStar_Extraction_ML_Syntax.loc = uu____7195;_},uu____7196);
             FStar_Extraction_ML_Syntax.mlty = uu____7197;
             FStar_Extraction_ML_Syntax.loc = uu____7198;_},_rid::init1::[])
          when
          let uu____7207 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7207 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7211 =
            let uu____7218 = translate_expr env init1  in
            (ManuallyManaged, uu____7218, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7211
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7222;
                  FStar_Extraction_ML_Syntax.loc = uu____7223;_},uu____7224);
             FStar_Extraction_ML_Syntax.mlty = uu____7225;
             FStar_Extraction_ML_Syntax.loc = uu____7226;_},_e0::e1::e2::[])
          when
          (((let uu____7238 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7238 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7243 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7243 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7248 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7248 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7253 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7253 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7257 =
            let uu____7264 = translate_expr env e1  in
            let uu____7265 = translate_expr env e2  in
            (ManuallyManaged, uu____7264, uu____7265)  in
          EBufCreate uu____7257
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7267;
                  FStar_Extraction_ML_Syntax.loc = uu____7268;_},uu____7269);
             FStar_Extraction_ML_Syntax.mlty = uu____7270;
             FStar_Extraction_ML_Syntax.loc = uu____7271;_},_erid::elen::[])
          when
          let uu____7280 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7280 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7284 =
            let uu____7289 = translate_expr env elen  in
            (ManuallyManaged, uu____7289)  in
          EBufCreateNoInit uu____7284
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
             FStar_Extraction_ML_Syntax.loc = uu____7295;_},e2::[])
          when
          let uu____7303 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7303 = "FStar.HyperStack.ST.rfree" ->
          let uu____7307 = translate_expr env e2  in EBufFree uu____7307
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7309;
                  FStar_Extraction_ML_Syntax.loc = uu____7310;_},uu____7311);
             FStar_Extraction_ML_Syntax.mlty = uu____7312;
             FStar_Extraction_ML_Syntax.loc = uu____7313;_},e2::[])
          when
          (let uu____7323 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7323 = "FStar.Buffer.rfree") ||
            (let uu____7328 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7328 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7332 = translate_expr env e2  in EBufFree uu____7332
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7334;
                  FStar_Extraction_ML_Syntax.loc = uu____7335;_},uu____7336);
             FStar_Extraction_ML_Syntax.mlty = uu____7337;
             FStar_Extraction_ML_Syntax.loc = uu____7338;_},e1::e2::_e3::[])
          when
          let uu____7348 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7348 = "FStar.Buffer.sub" ->
          let uu____7352 =
            let uu____7357 = translate_expr env e1  in
            let uu____7358 = translate_expr env e2  in
            (uu____7357, uu____7358)  in
          EBufSub uu____7352
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
             FStar_Extraction_ML_Syntax.loc = uu____7364;_},e1::e2::_e3::[])
          when
          let uu____7374 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7374 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____7378 =
            let uu____7383 = translate_expr env e1  in
            let uu____7384 = translate_expr env e2  in
            (uu____7383, uu____7384)  in
          EBufSub uu____7378
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7386;
                  FStar_Extraction_ML_Syntax.loc = uu____7387;_},uu____7388);
             FStar_Extraction_ML_Syntax.mlty = uu____7389;
             FStar_Extraction_ML_Syntax.loc = uu____7390;_},e1::e2::[])
          when
          let uu____7399 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7399 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7404;
                  FStar_Extraction_ML_Syntax.loc = uu____7405;_},uu____7406);
             FStar_Extraction_ML_Syntax.mlty = uu____7407;
             FStar_Extraction_ML_Syntax.loc = uu____7408;_},e1::e2::[])
          when
          let uu____7417 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7417 = "FStar.Buffer.offset" ->
          let uu____7421 =
            let uu____7426 = translate_expr env e1  in
            let uu____7427 = translate_expr env e2  in
            (uu____7426, uu____7427)  in
          EBufSub uu____7421
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7429;
                  FStar_Extraction_ML_Syntax.loc = uu____7430;_},uu____7431);
             FStar_Extraction_ML_Syntax.mlty = uu____7432;
             FStar_Extraction_ML_Syntax.loc = uu____7433;_},e1::e2::[])
          when
          let uu____7442 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7442 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7446 =
            let uu____7451 = translate_expr env e1  in
            let uu____7452 = translate_expr env e2  in
            (uu____7451, uu____7452)  in
          EBufSub uu____7446
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7454;
                  FStar_Extraction_ML_Syntax.loc = uu____7455;_},uu____7456);
             FStar_Extraction_ML_Syntax.mlty = uu____7457;
             FStar_Extraction_ML_Syntax.loc = uu____7458;_},e1::e2::e3::[])
          when
          (((let uu____7470 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7470 = "FStar.Buffer.upd") ||
              (let uu____7475 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7475 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7480 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7480 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7485 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7485 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7489 =
            let uu____7496 = translate_expr env e1  in
            let uu____7497 = translate_expr env e2  in
            let uu____7498 = translate_expr env e3  in
            (uu____7496, uu____7497, uu____7498)  in
          EBufWrite uu____7489
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
             FStar_Extraction_ML_Syntax.loc = uu____7504;_},e1::e2::[])
          when
          let uu____7513 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7513 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7517 =
            let uu____7524 = translate_expr env e1  in
            let uu____7525 = translate_expr env e2  in
            (uu____7524, (EConstant (UInt32, "0")), uu____7525)  in
          EBufWrite uu____7517
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7529;
             FStar_Extraction_ML_Syntax.loc = uu____7530;_},uu____7531::[])
          when
          let uu____7534 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7534 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7539;
             FStar_Extraction_ML_Syntax.loc = uu____7540;_},uu____7541::[])
          when
          let uu____7544 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7544 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
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
             FStar_Extraction_ML_Syntax.loc = uu____7553;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7567 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7567 = "FStar.Buffer.blit") ||
             (let uu____7572 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7572 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7577 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7577 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7581 =
            let uu____7592 = translate_expr env e1  in
            let uu____7593 = translate_expr env e2  in
            let uu____7594 = translate_expr env e3  in
            let uu____7595 = translate_expr env e4  in
            let uu____7596 = translate_expr env e5  in
            (uu____7592, uu____7593, uu____7594, uu____7595, uu____7596)  in
          EBufBlit uu____7581
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7598;
                  FStar_Extraction_ML_Syntax.loc = uu____7599;_},uu____7600);
             FStar_Extraction_ML_Syntax.mlty = uu____7601;
             FStar_Extraction_ML_Syntax.loc = uu____7602;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7618 =
            let uu____7625 = translate_expr env e1  in
            let uu____7626 = translate_expr env e2  in
            let uu____7627 = translate_expr env e3  in
            (uu____7625, uu____7626, uu____7627)  in
          EBufFill uu____7618
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7629;
             FStar_Extraction_ML_Syntax.loc = uu____7630;_},uu____7631::[])
          when
          let uu____7634 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7634 = "FStar.HyperStack.ST.get" -> EUnit
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
             FStar_Extraction_ML_Syntax.loc = uu____7643;_},_ebuf::_eseq::[])
          when
          (((let uu____7654 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7654 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7659 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7659 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7664 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7664 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7669 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7669 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7674;
             FStar_Extraction_ML_Syntax.loc = uu____7675;_},e1::[])
          when
          let uu____7679 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7679 = "Obj.repr" ->
          let uu____7683 =
            let uu____7688 = translate_expr env e1  in (uu____7688, TAny)  in
          ECast uu____7683
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7691;
             FStar_Extraction_ML_Syntax.loc = uu____7692;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7708 = FStar_Util.must (mk_width m)  in
          let uu____7709 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7708 uu____7709 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7711;
             FStar_Extraction_ML_Syntax.loc = uu____7712;_},args)
          when is_bool_op op ->
          let uu____7726 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7726 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],"Mk");
             FStar_Extraction_ML_Syntax.mlty = uu____7728;
             FStar_Extraction_ML_Syntax.loc = uu____7729;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7731;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7732;_}::[])
          when is_machine_int m ->
          let uu____7757 =
            let uu____7763 = FStar_Util.must (mk_width m)  in (uu____7763, c)
             in
          EConstant uu____7757
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7766;
             FStar_Extraction_ML_Syntax.loc = uu____7767;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7769;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7770;_}::[])
          when is_machine_int m ->
          let uu____7795 =
            let uu____7801 = FStar_Util.must (mk_width m)  in (uu____7801, c)
             in
          EConstant uu____7795
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7804;
             FStar_Extraction_ML_Syntax.loc = uu____7805;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7807;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7808;_}::[])
          when is_machine_int m ->
          let uu____7833 =
            let uu____7839 = FStar_Util.must (mk_width m)  in (uu____7839, c)
             in
          EConstant uu____7833
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7841;
             FStar_Extraction_ML_Syntax.loc = uu____7842;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7844;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7845;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7858 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7860;
             FStar_Extraction_ML_Syntax.loc = uu____7861;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7863;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7864;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7881 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7883;
             FStar_Extraction_ML_Syntax.loc = uu____7884;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7886;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7887;_}::[])
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
               ("LowStar"::"Literal"::[],"buffer_of_literal");
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
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____7923 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____7926;
             FStar_Extraction_ML_Syntax.loc = uu____7927;_},arg::[])
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
            let uu____7955 =
              let uu____7960 = translate_expr env arg  in
              (uu____7960, (TInt UInt64))  in
            ECast uu____7955
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____7965 =
                 let uu____7970 = translate_expr env arg  in
                 (uu____7970, (TInt UInt32))  in
               ECast uu____7965)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____7975 =
                   let uu____7980 = translate_expr env arg  in
                   (uu____7980, (TInt UInt16))  in
                 ECast uu____7975)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____7985 =
                     let uu____7990 = translate_expr env arg  in
                     (uu____7990, (TInt UInt8))  in
                   ECast uu____7985)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____7995 =
                       let uu____8000 = translate_expr env arg  in
                       (uu____8000, (TInt Int64))  in
                     ECast uu____7995)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8005 =
                         let uu____8010 = translate_expr env arg  in
                         (uu____8010, (TInt Int32))  in
                       ECast uu____8005)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8015 =
                           let uu____8020 = translate_expr env arg  in
                           (uu____8020, (TInt Int16))  in
                         ECast uu____8015)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8025 =
                             let uu____8030 = translate_expr env arg  in
                             (uu____8030, (TInt Int8))  in
                           ECast uu____8025)
                        else
                          (let uu____8033 =
                             let uu____8040 =
                               let uu____8043 = translate_expr env arg  in
                               [uu____8043]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8040)
                              in
                           EApp uu____8033)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8063 =
            let uu____8070 = translate_expr env head1  in
            let uu____8071 = FStar_List.map (translate_expr env) args  in
            (uu____8070, uu____8071)  in
          EApp uu____8063
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8082 =
            let uu____8089 = translate_expr env head1  in
            let uu____8090 = FStar_List.map (translate_type env) ty_args  in
            (uu____8089, uu____8090)  in
          ETypApp uu____8082
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8098 =
            let uu____8103 = translate_expr env e1  in
            let uu____8104 = translate_type env t_to  in
            (uu____8103, uu____8104)  in
          ECast uu____8098
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8105,fields) ->
          let uu____8127 =
            let uu____8139 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8140 =
              FStar_List.map
                (fun uu____8162  ->
                   match uu____8162 with
                   | (field,expr) ->
                       let uu____8177 = translate_expr env expr  in
                       (field, uu____8177)) fields
               in
            (uu____8139, uu____8140)  in
          EFlat uu____8127
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8188 =
            let uu____8196 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8197 = translate_expr env e1  in
            (uu____8196, uu____8197, (FStar_Pervasives_Native.snd path))  in
          EField uu____8188
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8203 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8216) ->
          let uu____8221 =
            let uu____8223 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8223
             in
          failwith uu____8221
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8235 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8235
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8241 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8241
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8244,cons1),es) ->
          let uu____8259 =
            let uu____8269 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8270 = FStar_List.map (translate_expr env) es  in
            (uu____8269, cons1, uu____8270)  in
          ECons uu____8259
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8296 =
            let uu____8305 = translate_expr env1 body  in
            let uu____8306 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8305, uu____8306)  in
          EFun uu____8296
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8316 =
            let uu____8323 = translate_expr env e1  in
            let uu____8324 = translate_expr env e2  in
            let uu____8325 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8323, uu____8324, uu____8325)  in
          EIfThenElse uu____8316
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8327 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8335 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8351 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____8369 =
              let uu____8384 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8384)  in
            TApp uu____8369
          else TQualified lid
      | uu____8399 ->
          let uu____8400 =
            let uu____8402 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8402
             in
          failwith uu____8400

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
    fun uu____8436  ->
      match uu____8436 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8463 = translate_pat env pat  in
            (match uu____8463 with
             | (env1,pat1) ->
                 let uu____8474 = translate_expr env1 expr  in
                 (pat1, uu____8474))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8482  ->
    match uu___7_8482 with
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
          let uu____8549 =
            let uu____8550 =
              let uu____8556 = translate_width sw  in (uu____8556, s)  in
            PConstant uu____8550  in
          (env, uu____8549)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8566,cons1),ps) ->
          let uu____8581 =
            FStar_List.fold_left
              (fun uu____8601  ->
                 fun p1  ->
                   match uu____8601 with
                   | (env1,acc) ->
                       let uu____8621 = translate_pat env1 p1  in
                       (match uu____8621 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8581 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8651,ps) ->
          let uu____8673 =
            FStar_List.fold_left
              (fun uu____8710  ->
                 fun uu____8711  ->
                   match (uu____8710, uu____8711) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____8791 = translate_pat env1 p1  in
                       (match uu____8791 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8673 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____8862 =
            FStar_List.fold_left
              (fun uu____8882  ->
                 fun p1  ->
                   match uu____8882 with
                   | (env1,acc) ->
                       let uu____8902 = translate_pat env1 p1  in
                       (match uu____8902 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8862 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____8929 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____8935 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____8949 =
            let uu____8951 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____8951
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____8949
          then
            let uu____8966 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____8966
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____8993) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9011 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9013 ->
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
          let uu____9038 =
            let uu____9045 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9045)  in
          EApp uu____9038
