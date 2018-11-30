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
    match projectee with | DGlobal _0 -> true | uu____696 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____808 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____934 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1042 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1175 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1293 -> false
  
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
    match projectee with | StdCall  -> true | uu____1478 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1489 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1500 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1511 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1522 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1533 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1544 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1555 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1568 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1590 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1603 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1627 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1651 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1673 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1684 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1695 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1706 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1717 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1730 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1761 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1810 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1844 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1862 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1906 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1950 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1994 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2034 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2064 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2102 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2144 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2182 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2224 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2266 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2326 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2380 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2416 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2447 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2458 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2471 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2493 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2504 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2516 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2547 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2607 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2652 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2690 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2730 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2765 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2818 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2857 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2888 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2933 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2956 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____2980 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3011 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3022 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3033 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3044 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3055 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3066 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3077 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3088 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3099 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3110 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3121 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3132 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3143 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3154 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3165 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3176 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3187 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3198 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3209 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3220 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3231 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3242 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3253 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3264 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3275 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3286 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3299 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3322 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3349 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3392 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3425 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3471 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3505 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3516 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3527 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3538 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3549 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3560 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3571 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3582 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3593 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3604 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3653 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3673 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3692 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3712 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____3755 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____3766 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____3782 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____3815 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____3852 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____3916 -> false
  
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
  'Auu____4019 'Auu____4020 'Auu____4021 .
    ('Auu____4019 * 'Auu____4020 * 'Auu____4021) -> 'Auu____4019
  = fun uu____4032  -> match uu____4032 with | (x,uu____4040,uu____4041) -> x 
let snd3 :
  'Auu____4051 'Auu____4052 'Auu____4053 .
    ('Auu____4051 * 'Auu____4052 * 'Auu____4053) -> 'Auu____4052
  = fun uu____4064  -> match uu____4064 with | (uu____4071,x,uu____4073) -> x 
let thd3 :
  'Auu____4083 'Auu____4084 'Auu____4085 .
    ('Auu____4083 * 'Auu____4084 * 'Auu____4085) -> 'Auu____4085
  = fun uu____4096  -> match uu____4096 with | (uu____4103,uu____4104,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___280_4114  ->
    match uu___280_4114 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4126 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___281_4136  ->
    match uu___281_4136 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4145 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___282_4166  ->
    match uu___282_4166 with
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
    | uu____4211 -> FStar_Pervasives_Native.None
  
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
      let uu___288_4367 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___288_4367.names_t);
        module_name = (uu___288_4367.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___289_4381 = env  in
      {
        names = (uu___289_4381.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___289_4381.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4396 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4396 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___291_4420  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___290_4427 ->
          let uu____4429 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4429
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___293_4449  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___292_4458 ->
          let uu____4460 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4460
  
let add_binders :
  'Auu____4471 . env -> (Prims.string * 'Auu____4471) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4506  ->
             match uu____4506 with | (name,uu____4513) -> extend env1 name)
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
      | uu____4565 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____4784  ->
    match uu____4784 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____4833 = m  in
               match uu____4833 with
               | (path,uu____4848,uu____4849) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___295_4867  ->
                  match () with
                  | () ->
                      (FStar_Util.print1
                         "Attempting to translate module %s\n" m_name;
                       (let uu____4872 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____4872))) ()
             with
             | e ->
                 ((let uu____4881 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____4881);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____4884  ->
    match uu____4884 with
    | (module_name,modul,uu____4899) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____4934 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___283_4948  ->
         match uu___283_4948 with
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
         | uu____4959 -> FStar_Pervasives_Native.None) flags1

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags1  ->
    let uu____4963 =
      FStar_List.choose
        (fun uu___284_4970  ->
           match uu___284_4970 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____4977 -> FStar_Pervasives_Native.None) flags1
       in
    match uu____4963 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____4990 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5004 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5006 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5011) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5038;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5041;_} when
            FStar_Util.for_some
              (fun uu___285_5046  ->
                 match uu___285_5046 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5049 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____5070 =
                let uu____5071 =
                  let uu____5092 = translate_cc meta  in
                  let uu____5095 = translate_flags meta  in
                  let uu____5098 = translate_type env t0  in
                  (uu____5092, uu____5095, name1, uu____5098)  in
                DExternal uu____5071  in
              FStar_Pervasives_Native.Some uu____5070
            else
              ((let uu____5114 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5114);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5120;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5123;
                FStar_Extraction_ML_Syntax.loc = uu____5124;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5126;_} ->
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
               let rec find_return_type eff i uu___286_5183 =
                 match uu___286_5183 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5192,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5212 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5212 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5238 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5238 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5256) ->
                           let uu____5257 = translate_flags meta  in
                           MustDisappear :: uu____5257
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5260 = translate_flags meta  in
                           MustDisappear :: uu____5260
                       | uu____5263 -> translate_flags meta  in
                     try
                       (fun uu___297_5272  ->
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
                         ((let uu____5304 =
                             let uu____5310 =
                               let uu____5312 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5312 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5310)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5304);
                          (let msg1 =
                             Prims.strcat
                               "This function was not extracted:\n" msg
                              in
                           FStar_Pervasives_Native.Some
                             (DFunction
                                (cc, meta1, (FStar_List.length tvars), t1,
                                  name1, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5338;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5341;_} ->
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
                 (fun uu___299_5378  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5402 =
                       let uu____5408 =
                         let uu____5410 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5412 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5410
                           uu____5412
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5408)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5402);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5430;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5431;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5432;
            FStar_Extraction_ML_Syntax.print_typ = uu____5433;_} ->
            ((let uu____5440 =
                let uu____5446 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5446)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5440);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5453 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5453
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5467 = ty  in
      match uu____5467 with
      | (uu____5470,uu____5471,uu____5472,uu____5473,flags1,uu____5475) ->
          if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags1
          then FStar_Pervasives_Native.None
          else
            (match ty with
             | (assumed,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
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
                        flags2)
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
                     (let uu____5549 =
                        let uu____5550 =
                          let uu____5570 = translate_flags flags2  in
                          let uu____5573 = translate_type env1 t  in
                          (name1, uu____5570, (FStar_List.length args),
                            uu____5573)
                           in
                        DTypeAlias uu____5550  in
                      FStar_Pervasives_Native.Some uu____5549)
             | (uu____5586,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5631 =
                   let uu____5632 =
                     let uu____5664 = translate_flags flags2  in
                     let uu____5667 =
                       FStar_List.map
                         (fun uu____5699  ->
                            match uu____5699 with
                            | (f,t) ->
                                let uu____5719 =
                                  let uu____5725 = translate_type env1 t  in
                                  (uu____5725, false)  in
                                (f, uu____5719)) fields
                        in
                     (name1, uu____5664, (FStar_List.length args),
                       uu____5667)
                      in
                   DTypeFlat uu____5632  in
                 FStar_Pervasives_Native.Some uu____5631
             | (uu____5758,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____5808 =
                   let uu____5809 =
                     let uu____5848 =
                       FStar_List.map
                         (fun uu____5901  ->
                            match uu____5901 with
                            | (cons1,ts) ->
                                let uu____5949 =
                                  FStar_List.map
                                    (fun uu____5981  ->
                                       match uu____5981 with
                                       | (name2,t) ->
                                           let uu____6001 =
                                             let uu____6007 =
                                               translate_type env1 t  in
                                             (uu____6007, false)  in
                                           (name2, uu____6001)) ts
                                   in
                                (cons1, uu____5949)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____5848)
                      in
                   DTypeVariant uu____5809  in
                 FStar_Pervasives_Native.Some uu____5808
             | (uu____6060,name,_mangled_name,uu____6063,uu____6064,uu____6065)
                 ->
                 ((let uu____6081 =
                     let uu____6087 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6087)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6081);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6095 = find_t env name  in TBound uu____6095
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6098,t2) ->
          let uu____6100 =
            let uu____6105 = translate_type env t1  in
            let uu____6106 = translate_type env t2  in
            (uu____6105, uu____6106)  in
          TArrow uu____6100
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6110 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6110 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6117 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6117 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6134 = FStar_Util.must (mk_width m)  in TInt uu____6134
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6148 = FStar_Util.must (mk_width m)  in TInt uu____6148
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6153 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6153 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6157::arg::uu____6159::[],p) when
          (((let uu____6165 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6165 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6170 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6170 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6175 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6175 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6180 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6180 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6184 = translate_type env arg  in TBuf uu____6184
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6186::[],p) when
          ((((((((((let uu____6192 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6192 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6197 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6197 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6202 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6202 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6207 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6207 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6212 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6212 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6217 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6217 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6222 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6222 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6227 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6227 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6232 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6232 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6237 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6237 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6242 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6242 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6246 = translate_type env arg  in TBuf uu____6246
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6248::uu____6249::[],p) when
          let uu____6253 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6253 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6257 = translate_type env arg  in TBuf uu____6257
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6264 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6264 = "FStar.Buffer.buffer") ||
                        (let uu____6269 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6269 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6274 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6274 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6279 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6279 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6284 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6284 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6289 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6289 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6294 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6294 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6299 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6299 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6304 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6304 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6309 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6309 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6314 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6314 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6319 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6319 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6324 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6324 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6329 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6329 = "FStar.HyperStack.ST.mmref")
          -> let uu____6333 = translate_type env arg  in TBuf uu____6333
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6334::arg::[],p) when
          (let uu____6341 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6341 = "FStar.HyperStack.s_ref") ||
            (let uu____6346 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6346 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6350 = translate_type env arg  in TBuf uu____6350
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6351::[],p) when
          let uu____6355 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6355 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6407 = FStar_List.map (translate_type env) args  in
          TTuple uu____6407
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____6418 =
              let uu____6433 = FStar_List.map (translate_type env) args  in
              (lid, uu____6433)  in
            TApp uu____6418
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6451 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6451

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
    fun uu____6469  ->
      match uu____6469 with
      | (name,typ) ->
          let uu____6479 = translate_type env typ  in
          { name; typ = uu____6479; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6486 = find env name  in EBound uu____6486
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6500 =
            let uu____6505 = FStar_Util.must (mk_op op)  in
            let uu____6506 = FStar_Util.must (mk_width m)  in
            (uu____6505, uu____6506)  in
          EOp uu____6500
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6516 =
            let uu____6521 = FStar_Util.must (mk_bool_op op)  in
            (uu____6521, Bool)  in
          EOp uu____6516
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                     FStar_Extraction_ML_Syntax.mllb_tysc =
                       FStar_Pervasives_Native.Some ([],typ);
                     FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
                     FStar_Extraction_ML_Syntax.mllb_def = body;
                     FStar_Extraction_ML_Syntax.mllb_meta = flags1;
                     FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let binder =
            let uu____6544 = translate_type env typ  in
            { name; typ = uu____6544; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6571 =
            let uu____6582 = translate_expr env expr  in
            let uu____6583 = translate_branches env branches  in
            (uu____6582, uu____6583)  in
          EMatch uu____6571
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6597;
                  FStar_Extraction_ML_Syntax.loc = uu____6598;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6600;
             FStar_Extraction_ML_Syntax.loc = uu____6601;_},arg::[])
          when
          let uu____6607 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6607 = "FStar.Dyn.undyn" ->
          let uu____6611 =
            let uu____6616 = translate_expr env arg  in
            let uu____6617 = translate_type env t  in
            (uu____6616, uu____6617)  in
          ECast uu____6611
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6619;
                  FStar_Extraction_ML_Syntax.loc = uu____6620;_},uu____6621);
             FStar_Extraction_ML_Syntax.mlty = uu____6622;
             FStar_Extraction_ML_Syntax.loc = uu____6623;_},uu____6624)
          when
          let uu____6633 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6633 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6638;
                  FStar_Extraction_ML_Syntax.loc = uu____6639;_},uu____6640);
             FStar_Extraction_ML_Syntax.mlty = uu____6641;
             FStar_Extraction_ML_Syntax.loc = uu____6642;_},arg::[])
          when
          ((let uu____6652 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6652 = "FStar.HyperStack.All.failwith") ||
             (let uu____6657 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6657 = "FStar.Error.unexpected"))
            ||
            (let uu____6662 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6662 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6667;
               FStar_Extraction_ML_Syntax.loc = uu____6668;_} -> EAbortS msg
           | uu____6670 ->
               let print7 =
                 let uu____6672 =
                   let uu____6673 =
                     let uu____6674 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6674
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6673  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6672
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6681;
                  FStar_Extraction_ML_Syntax.loc = uu____6682;_},uu____6683);
             FStar_Extraction_ML_Syntax.mlty = uu____6684;
             FStar_Extraction_ML_Syntax.loc = uu____6685;_},e1::[])
          when
          (let uu____6695 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6695 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6700 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6700 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6705;
                  FStar_Extraction_ML_Syntax.loc = uu____6706;_},uu____6707);
             FStar_Extraction_ML_Syntax.mlty = uu____6708;
             FStar_Extraction_ML_Syntax.loc = uu____6709;_},e1::e2::[])
          when
          (((let uu____6720 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6720 = "FStar.Buffer.index") ||
              (let uu____6725 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6725 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____6730 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6730 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____6735 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6735 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____6739 =
            let uu____6744 = translate_expr env e1  in
            let uu____6745 = translate_expr env e2  in
            (uu____6744, uu____6745)  in
          EBufRead uu____6739
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6747;
                  FStar_Extraction_ML_Syntax.loc = uu____6748;_},uu____6749);
             FStar_Extraction_ML_Syntax.mlty = uu____6750;
             FStar_Extraction_ML_Syntax.loc = uu____6751;_},e1::[])
          when
          let uu____6759 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6759 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6763 =
            let uu____6768 = translate_expr env e1  in
            (uu____6768, (EConstant (UInt32, "0")))  in
          EBufRead uu____6763
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6772;
                  FStar_Extraction_ML_Syntax.loc = uu____6773;_},uu____6774);
             FStar_Extraction_ML_Syntax.mlty = uu____6775;
             FStar_Extraction_ML_Syntax.loc = uu____6776;_},e1::e2::[])
          when
          ((let uu____6787 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6787 = "FStar.Buffer.create") ||
             (let uu____6792 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6792 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____6797 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6797 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____6801 =
            let uu____6808 = translate_expr env e1  in
            let uu____6809 = translate_expr env e2  in
            (Stack, uu____6808, uu____6809)  in
          EBufCreate uu____6801
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6811;
                  FStar_Extraction_ML_Syntax.loc = uu____6812;_},uu____6813);
             FStar_Extraction_ML_Syntax.mlty = uu____6814;
             FStar_Extraction_ML_Syntax.loc = uu____6815;_},elen::[])
          when
          let uu____6823 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6823 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____6827 =
            let uu____6832 = translate_expr env elen  in (Stack, uu____6832)
             in
          EBufCreateNoInit uu____6827
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6834;
                  FStar_Extraction_ML_Syntax.loc = uu____6835;_},uu____6836);
             FStar_Extraction_ML_Syntax.mlty = uu____6837;
             FStar_Extraction_ML_Syntax.loc = uu____6838;_},init1::[])
          when
          let uu____6846 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6846 = "FStar.HyperStack.ST.salloc" ->
          let uu____6850 =
            let uu____6857 = translate_expr env init1  in
            (Stack, uu____6857, (EConstant (UInt32, "1")))  in
          EBufCreate uu____6850
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6861;
                  FStar_Extraction_ML_Syntax.loc = uu____6862;_},uu____6863);
             FStar_Extraction_ML_Syntax.mlty = uu____6864;
             FStar_Extraction_ML_Syntax.loc = uu____6865;_},e2::[])
          when
          ((let uu____6875 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6875 = "FStar.Buffer.createL") ||
             (let uu____6880 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6880 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____6885 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6885 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____6889 =
            let uu____6896 =
              let uu____6899 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____6899  in
            (Stack, uu____6896)  in
          EBufCreateL uu____6889
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6905;
                  FStar_Extraction_ML_Syntax.loc = uu____6906;_},uu____6907);
             FStar_Extraction_ML_Syntax.mlty = uu____6908;
             FStar_Extraction_ML_Syntax.loc = uu____6909;_},_erid::e2::[])
          when
          (let uu____6920 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6920 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____6925 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6925 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____6929 =
            let uu____6936 =
              let uu____6939 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____6939  in
            (Eternal, uu____6936)  in
          EBufCreateL uu____6929
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6945;
                  FStar_Extraction_ML_Syntax.loc = uu____6946;_},uu____6947);
             FStar_Extraction_ML_Syntax.mlty = uu____6948;
             FStar_Extraction_ML_Syntax.loc = uu____6949;_},_rid::init1::[])
          when
          let uu____6958 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6958 = "FStar.HyperStack.ST.ralloc" ->
          let uu____6962 =
            let uu____6969 = translate_expr env init1  in
            (Eternal, uu____6969, (EConstant (UInt32, "1")))  in
          EBufCreate uu____6962
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
             FStar_Extraction_ML_Syntax.loc = uu____6977;_},_e0::e1::e2::[])
          when
          ((let uu____6989 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6989 = "FStar.Buffer.rcreate") ||
             (let uu____6994 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6994 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____6999 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6999 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7003 =
            let uu____7010 = translate_expr env e1  in
            let uu____7011 = translate_expr env e2  in
            (Eternal, uu____7010, uu____7011)  in
          EBufCreate uu____7003
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7013;
                  FStar_Extraction_ML_Syntax.loc = uu____7014;_},uu____7015);
             FStar_Extraction_ML_Syntax.mlty = uu____7016;
             FStar_Extraction_ML_Syntax.loc = uu____7017;_},_erid::elen::[])
          when
          let uu____7026 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7026 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7030 =
            let uu____7035 = translate_expr env elen  in
            (Eternal, uu____7035)  in
          EBufCreateNoInit uu____7030
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
             FStar_Extraction_ML_Syntax.loc = uu____7041;_},_rid::init1::[])
          when
          let uu____7050 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7050 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7054 =
            let uu____7061 = translate_expr env init1  in
            (ManuallyManaged, uu____7061, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7054
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7065;
                  FStar_Extraction_ML_Syntax.loc = uu____7066;_},uu____7067);
             FStar_Extraction_ML_Syntax.mlty = uu____7068;
             FStar_Extraction_ML_Syntax.loc = uu____7069;_},_e0::e1::e2::[])
          when
          (((let uu____7081 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7081 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7086 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7086 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7091 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7091 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7096 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7096 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7100 =
            let uu____7107 = translate_expr env e1  in
            let uu____7108 = translate_expr env e2  in
            (ManuallyManaged, uu____7107, uu____7108)  in
          EBufCreate uu____7100
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7110;
                  FStar_Extraction_ML_Syntax.loc = uu____7111;_},uu____7112);
             FStar_Extraction_ML_Syntax.mlty = uu____7113;
             FStar_Extraction_ML_Syntax.loc = uu____7114;_},_erid::elen::[])
          when
          let uu____7123 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7123 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7127 =
            let uu____7132 = translate_expr env elen  in
            (ManuallyManaged, uu____7132)  in
          EBufCreateNoInit uu____7127
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7134;
                  FStar_Extraction_ML_Syntax.loc = uu____7135;_},uu____7136);
             FStar_Extraction_ML_Syntax.mlty = uu____7137;
             FStar_Extraction_ML_Syntax.loc = uu____7138;_},e2::[])
          when
          let uu____7146 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7146 = "FStar.HyperStack.ST.rfree" ->
          let uu____7150 = translate_expr env e2  in EBufFree uu____7150
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7152;
                  FStar_Extraction_ML_Syntax.loc = uu____7153;_},uu____7154);
             FStar_Extraction_ML_Syntax.mlty = uu____7155;
             FStar_Extraction_ML_Syntax.loc = uu____7156;_},e2::[])
          when
          (let uu____7166 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7166 = "FStar.Buffer.rfree") ||
            (let uu____7171 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7171 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7175 = translate_expr env e2  in EBufFree uu____7175
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7177;
                  FStar_Extraction_ML_Syntax.loc = uu____7178;_},uu____7179);
             FStar_Extraction_ML_Syntax.mlty = uu____7180;
             FStar_Extraction_ML_Syntax.loc = uu____7181;_},e1::e2::_e3::[])
          when
          let uu____7191 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7191 = "FStar.Buffer.sub" ->
          let uu____7195 =
            let uu____7200 = translate_expr env e1  in
            let uu____7201 = translate_expr env e2  in
            (uu____7200, uu____7201)  in
          EBufSub uu____7195
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7203;
                  FStar_Extraction_ML_Syntax.loc = uu____7204;_},uu____7205);
             FStar_Extraction_ML_Syntax.mlty = uu____7206;
             FStar_Extraction_ML_Syntax.loc = uu____7207;_},e1::e2::_e3::[])
          when
          let uu____7217 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7217 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____7221 =
            let uu____7226 = translate_expr env e1  in
            let uu____7227 = translate_expr env e2  in
            (uu____7226, uu____7227)  in
          EBufSub uu____7221
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7229;
                  FStar_Extraction_ML_Syntax.loc = uu____7230;_},uu____7231);
             FStar_Extraction_ML_Syntax.mlty = uu____7232;
             FStar_Extraction_ML_Syntax.loc = uu____7233;_},e1::e2::[])
          when
          let uu____7242 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7242 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7247;
                  FStar_Extraction_ML_Syntax.loc = uu____7248;_},uu____7249);
             FStar_Extraction_ML_Syntax.mlty = uu____7250;
             FStar_Extraction_ML_Syntax.loc = uu____7251;_},e1::e2::[])
          when
          let uu____7260 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7260 = "FStar.Buffer.offset" ->
          let uu____7264 =
            let uu____7269 = translate_expr env e1  in
            let uu____7270 = translate_expr env e2  in
            (uu____7269, uu____7270)  in
          EBufSub uu____7264
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7272;
                  FStar_Extraction_ML_Syntax.loc = uu____7273;_},uu____7274);
             FStar_Extraction_ML_Syntax.mlty = uu____7275;
             FStar_Extraction_ML_Syntax.loc = uu____7276;_},e1::e2::[])
          when
          let uu____7285 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7285 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7289 =
            let uu____7294 = translate_expr env e1  in
            let uu____7295 = translate_expr env e2  in
            (uu____7294, uu____7295)  in
          EBufSub uu____7289
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7297;
                  FStar_Extraction_ML_Syntax.loc = uu____7298;_},uu____7299);
             FStar_Extraction_ML_Syntax.mlty = uu____7300;
             FStar_Extraction_ML_Syntax.loc = uu____7301;_},e1::e2::e3::[])
          when
          (((let uu____7313 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7313 = "FStar.Buffer.upd") ||
              (let uu____7318 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7318 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7323 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7323 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7328 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7328 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7332 =
            let uu____7339 = translate_expr env e1  in
            let uu____7340 = translate_expr env e2  in
            let uu____7341 = translate_expr env e3  in
            (uu____7339, uu____7340, uu____7341)  in
          EBufWrite uu____7332
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7343;
                  FStar_Extraction_ML_Syntax.loc = uu____7344;_},uu____7345);
             FStar_Extraction_ML_Syntax.mlty = uu____7346;
             FStar_Extraction_ML_Syntax.loc = uu____7347;_},e1::e2::[])
          when
          let uu____7356 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7356 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7360 =
            let uu____7367 = translate_expr env e1  in
            let uu____7368 = translate_expr env e2  in
            (uu____7367, (EConstant (UInt32, "0")), uu____7368)  in
          EBufWrite uu____7360
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7372;
             FStar_Extraction_ML_Syntax.loc = uu____7373;_},uu____7374::[])
          when
          let uu____7377 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7377 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7382;
             FStar_Extraction_ML_Syntax.loc = uu____7383;_},uu____7384::[])
          when
          let uu____7387 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7387 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7392;
                  FStar_Extraction_ML_Syntax.loc = uu____7393;_},uu____7394);
             FStar_Extraction_ML_Syntax.mlty = uu____7395;
             FStar_Extraction_ML_Syntax.loc = uu____7396;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7410 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7410 = "FStar.Buffer.blit") ||
             (let uu____7415 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7415 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7420 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7420 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7424 =
            let uu____7435 = translate_expr env e1  in
            let uu____7436 = translate_expr env e2  in
            let uu____7437 = translate_expr env e3  in
            let uu____7438 = translate_expr env e4  in
            let uu____7439 = translate_expr env e5  in
            (uu____7435, uu____7436, uu____7437, uu____7438, uu____7439)  in
          EBufBlit uu____7424
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7441;
                  FStar_Extraction_ML_Syntax.loc = uu____7442;_},uu____7443);
             FStar_Extraction_ML_Syntax.mlty = uu____7444;
             FStar_Extraction_ML_Syntax.loc = uu____7445;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7461 =
            let uu____7468 = translate_expr env e1  in
            let uu____7469 = translate_expr env e2  in
            let uu____7470 = translate_expr env e3  in
            (uu____7468, uu____7469, uu____7470)  in
          EBufFill uu____7461
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7472;
             FStar_Extraction_ML_Syntax.loc = uu____7473;_},uu____7474::[])
          when
          let uu____7477 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7477 = "FStar.HyperStack.ST.get" -> EUnit
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
             FStar_Extraction_ML_Syntax.loc = uu____7486;_},_ebuf::_eseq::[])
          when
          (((let uu____7497 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7497 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7502 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7502 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7507 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7507 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7512 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7512 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7517;
             FStar_Extraction_ML_Syntax.loc = uu____7518;_},e1::[])
          when
          let uu____7522 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7522 = "Obj.repr" ->
          let uu____7526 =
            let uu____7531 = translate_expr env e1  in (uu____7531, TAny)  in
          ECast uu____7526
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7534;
             FStar_Extraction_ML_Syntax.loc = uu____7535;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7551 = FStar_Util.must (mk_width m)  in
          let uu____7552 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7551 uu____7552 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7554;
             FStar_Extraction_ML_Syntax.loc = uu____7555;_},args)
          when is_bool_op op ->
          let uu____7569 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7569 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7571;
             FStar_Extraction_ML_Syntax.loc = uu____7572;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7574;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7575;_}::[])
          when is_machine_int m ->
          let uu____7600 =
            let uu____7606 = FStar_Util.must (mk_width m)  in (uu____7606, c)
             in
          EConstant uu____7600
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7609;
             FStar_Extraction_ML_Syntax.loc = uu____7610;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7612;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7613;_}::[])
          when is_machine_int m ->
          let uu____7638 =
            let uu____7644 = FStar_Util.must (mk_width m)  in (uu____7644, c)
             in
          EConstant uu____7638
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7646;
             FStar_Extraction_ML_Syntax.loc = uu____7647;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7649;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7650;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7663 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7665;
             FStar_Extraction_ML_Syntax.loc = uu____7666;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7668;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7669;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7684 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____7687;
             FStar_Extraction_ML_Syntax.loc = uu____7688;_},arg::[])
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
            let uu____7716 =
              let uu____7721 = translate_expr env arg  in
              (uu____7721, (TInt UInt64))  in
            ECast uu____7716
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____7726 =
                 let uu____7731 = translate_expr env arg  in
                 (uu____7731, (TInt UInt32))  in
               ECast uu____7726)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____7736 =
                   let uu____7741 = translate_expr env arg  in
                   (uu____7741, (TInt UInt16))  in
                 ECast uu____7736)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____7746 =
                     let uu____7751 = translate_expr env arg  in
                     (uu____7751, (TInt UInt8))  in
                   ECast uu____7746)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____7756 =
                       let uu____7761 = translate_expr env arg  in
                       (uu____7761, (TInt Int64))  in
                     ECast uu____7756)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____7766 =
                         let uu____7771 = translate_expr env arg  in
                         (uu____7771, (TInt Int32))  in
                       ECast uu____7766)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____7776 =
                           let uu____7781 = translate_expr env arg  in
                           (uu____7781, (TInt Int16))  in
                         ECast uu____7776)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____7786 =
                             let uu____7791 = translate_expr env arg  in
                             (uu____7791, (TInt Int8))  in
                           ECast uu____7786)
                        else
                          (let uu____7794 =
                             let uu____7801 =
                               let uu____7804 = translate_expr env arg  in
                               [uu____7804]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____7801)
                              in
                           EApp uu____7794)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____7824 =
            let uu____7831 = translate_expr env head1  in
            let uu____7832 = FStar_List.map (translate_expr env) args  in
            (uu____7831, uu____7832)  in
          EApp uu____7824
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____7843 =
            let uu____7850 = translate_expr env head1  in
            let uu____7851 = FStar_List.map (translate_type env) ty_args  in
            (uu____7850, uu____7851)  in
          ETypApp uu____7843
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____7859 =
            let uu____7864 = translate_expr env e1  in
            let uu____7865 = translate_type env t_to  in
            (uu____7864, uu____7865)  in
          ECast uu____7859
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____7866,fields) ->
          let uu____7888 =
            let uu____7900 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____7901 =
              FStar_List.map
                (fun uu____7923  ->
                   match uu____7923 with
                   | (field,expr) ->
                       let uu____7938 = translate_expr env expr  in
                       (field, uu____7938)) fields
               in
            (uu____7900, uu____7901)  in
          EFlat uu____7888
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____7949 =
            let uu____7957 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____7958 = translate_expr env e1  in
            (uu____7957, uu____7958, (FStar_Pervasives_Native.snd path))  in
          EField uu____7949
      | FStar_Extraction_ML_Syntax.MLE_Let uu____7964 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____7977) ->
          let uu____7982 =
            let uu____7984 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____7984
             in
          failwith uu____7982
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____7996 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____7996
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8002 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8002
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8005,cons1),es) ->
          let uu____8020 =
            let uu____8030 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8031 = FStar_List.map (translate_expr env) es  in
            (uu____8030, cons1, uu____8031)  in
          ECons uu____8020
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8057 =
            let uu____8066 = translate_expr env1 body  in
            let uu____8067 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8066, uu____8067)  in
          EFun uu____8057
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8077 =
            let uu____8084 = translate_expr env e1  in
            let uu____8085 = translate_expr env e2  in
            let uu____8086 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8084, uu____8085, uu____8086)  in
          EIfThenElse uu____8077
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8088 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8096 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8112 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____8130 =
              let uu____8145 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8145)  in
            TApp uu____8130
          else TQualified lid
      | uu____8160 -> failwith "invalid argument: assert_lid"

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
    fun uu____8187  ->
      match uu____8187 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8214 = translate_pat env pat  in
            (match uu____8214 with
             | (env1,pat1) ->
                 let uu____8225 = translate_expr env1 expr  in
                 (pat1, uu____8225))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___287_8233  ->
    match uu___287_8233 with
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
          let uu____8300 =
            let uu____8301 =
              let uu____8307 = translate_width sw  in (uu____8307, s)  in
            PConstant uu____8301  in
          (env, uu____8300)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8317,cons1),ps) ->
          let uu____8332 =
            FStar_List.fold_left
              (fun uu____8352  ->
                 fun p1  ->
                   match uu____8352 with
                   | (env1,acc) ->
                       let uu____8372 = translate_pat env1 p1  in
                       (match uu____8372 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8332 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8402,ps) ->
          let uu____8424 =
            FStar_List.fold_left
              (fun uu____8461  ->
                 fun uu____8462  ->
                   match (uu____8461, uu____8462) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____8542 = translate_pat env1 p1  in
                       (match uu____8542 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8424 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____8613 =
            FStar_List.fold_left
              (fun uu____8633  ->
                 fun p1  ->
                   match uu____8633 with
                   | (env1,acc) ->
                       let uu____8653 = translate_pat env1 p1  in
                       (match uu____8653 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8613 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____8680 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____8686 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____8700 =
            let uu____8702 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____8702
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____8700
          then
            let uu____8717 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____8717
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____8744) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____8762 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____8764 ->
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
          let uu____8788 =
            let uu____8795 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____8795)  in
          EApp uu____8788
