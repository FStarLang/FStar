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
  fun projectee ->
    match projectee with | DGlobal _0 -> true | uu____753 -> false
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee -> match projectee with | DGlobal _0 -> _0
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DFunction _0 -> true | uu____864 -> false
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee -> match projectee with | DFunction _0 -> _0
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeAlias _0 -> true | uu____989 -> false
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee -> match projectee with | DTypeAlias _0 -> _0
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeFlat _0 -> true | uu____1096 -> false
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee -> match projectee with | DTypeFlat _0 -> _0
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1228 -> false
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeVariant _0 -> true | uu____1345 -> false
let (__proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list)
      Prims.list))
  = fun projectee -> match projectee with | DTypeVariant _0 -> _0
let (uu___is_DTypeAbstractStruct : decl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | DTypeAbstractStruct _0 -> true
    | uu____1486 -> false
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | DTypeAbstractStruct _0 -> _0
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DExternal _0 -> true | uu____1554 -> false
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee -> match projectee with | DExternal _0 -> _0
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | StdCall -> true | uu____1647 -> false
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee -> match projectee with | CDecl -> true | uu____1658 -> false
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | FastCall -> true | uu____1669 -> false
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Private -> true | uu____1680 -> false
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | WipeBody -> true | uu____1691 -> false
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CInline -> true | uu____1702 -> false
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Substitute -> true | uu____1713 -> false
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | GCType -> true | uu____1724 -> false
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Comment _0 -> true | uu____1737 -> false
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | MustDisappear -> true | uu____1758 -> false
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____1771 -> false
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Prologue _0 -> true | uu____1794 -> false
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Prologue _0 -> _0
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Epilogue _0 -> true | uu____1817 -> false
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Epilogue _0 -> _0
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Abstract -> true | uu____1838 -> false
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee -> match projectee with | IfDef -> true | uu____1849 -> false
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee -> match projectee with | Macro -> true | uu____1860 -> false
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Deprecated _0 -> true | uu____1873 -> false
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Deprecated _0 -> _0
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | Eternal -> true | uu____1894 -> false
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee -> match projectee with | Stack -> true | uu____1905 -> false
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | ManuallyManaged -> true | uu____1916 -> false
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBound _0 -> true | uu____1929 -> false
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee -> match projectee with | EBound _0 -> _0
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EQualified _0 -> true | uu____1959 -> false
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | EQualified _0 -> _0
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EConstant _0 -> true | uu____2007 -> false
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee -> match projectee with | EConstant _0 -> _0
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee -> match projectee with | EUnit -> true | uu____2040 -> false
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EApp _0 -> true | uu____2058 -> false
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee -> match projectee with | EApp _0 -> _0
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETypApp _0 -> true | uu____2101 -> false
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee -> match projectee with | ETypApp _0 -> _0
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ELet _0 -> true | uu____2144 -> false
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee -> match projectee with | ELet _0 -> _0
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EIfThenElse _0 -> true | uu____2187 -> false
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EIfThenElse _0 -> _0
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ESequence _0 -> true | uu____2226 -> false
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ESequence _0 -> _0
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAssign _0 -> true | uu____2255 -> false
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EAssign _0 -> _0
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreate _0 -> true | uu____2292 -> false
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee -> match projectee with | EBufCreate _0 -> _0
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufRead _0 -> true | uu____2333 -> false
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufRead _0 -> _0
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufWrite _0 -> true | uu____2370 -> false
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EBufWrite _0 -> _0
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufSub _0 -> true | uu____2411 -> false
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufSub _0 -> _0
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufBlit _0 -> true | uu____2452 -> false
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee -> match projectee with | EBufBlit _0 -> _0
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EMatch _0 -> true | uu____2511 -> false
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee -> match projectee with | EMatch _0 -> _0
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EOp _0 -> true | uu____2564 -> false
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee -> match projectee with | EOp _0 -> _0
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECast _0 -> true | uu____2599 -> false
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee -> match projectee with | ECast _0 -> _0
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPushFrame -> true | uu____2629 -> false
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPopFrame -> true | uu____2640 -> false
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBool _0 -> true | uu____2653 -> false
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBool _0 -> _0
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAny -> true | uu____2674 -> false
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbort -> true | uu____2685 -> false
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EReturn _0 -> true | uu____2697 -> false
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EReturn _0 -> _0
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFlat _0 -> true | uu____2727 -> false
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee -> match projectee with | EFlat _0 -> _0
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EField _0 -> true | uu____2786 -> false
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee -> match projectee with | EField _0 -> _0
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EWhile _0 -> true | uu____2830 -> false
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EWhile _0 -> _0
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateL _0 -> true | uu____2867 -> false
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee -> match projectee with | EBufCreateL _0 -> _0
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETuple _0 -> true | uu____2906 -> false
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ETuple _0 -> _0
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECons _0 -> true | uu____2940 -> false
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee -> match projectee with | ECons _0 -> _0
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFill _0 -> true | uu____2992 -> false
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EBufFill _0 -> _0
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EString _0 -> true | uu____3030 -> false
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EString _0 -> _0
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFun _0 -> true | uu____3060 -> false
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee -> match projectee with | EFun _0 -> _0
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbortS _0 -> true | uu____3104 -> false
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EAbortS _0 -> _0
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFree _0 -> true | uu____3126 -> false
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EBufFree _0 -> _0
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____3149 -> false
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee -> match projectee with | EBufCreateNoInit _0 -> _0
let (uu___is_EAbortT : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbortT _0 -> true | uu____3185 -> false
let (__proj__EAbortT__item___0 : expr -> (Prims.string * typ)) =
  fun projectee -> match projectee with | EAbortT _0 -> _0
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu____3218 -> false
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee -> match projectee with | AddW -> true | uu____3229 -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu____3240 -> false
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee -> match projectee with | SubW -> true | uu____3251 -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu____3262 -> false
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee -> match projectee with | DivW -> true | uu____3273 -> false
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee -> match projectee with | Mult -> true | uu____3284 -> false
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee -> match projectee with | MultW -> true | uu____3295 -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu____3306 -> false
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BOr -> true | uu____3317 -> false
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BAnd -> true | uu____3328 -> false
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BXor -> true | uu____3339 -> false
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftL -> true | uu____3350 -> false
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftR -> true | uu____3361 -> false
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee -> match projectee with | BNot -> true | uu____3372 -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu____3383 -> false
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee -> match projectee with | Neq -> true | uu____3394 -> false
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu____3405 -> false
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee -> match projectee with | Lte -> true | uu____3416 -> false
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu____3427 -> false
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee -> match projectee with | Gte -> true | uu____3438 -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu____3449 -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu____3460 -> false
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee -> match projectee with | Xor -> true | uu____3471 -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu____3482 -> false
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PUnit -> true | uu____3493 -> false
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PBool _0 -> true | uu____3506 -> false
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PBool _0 -> _0
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PVar _0 -> true | uu____3528 -> false
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee -> match projectee with | PVar _0 -> _0
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PCons _0 -> true | uu____3554 -> false
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee -> match projectee with | PCons _0 -> _0
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PTuple _0 -> true | uu____3596 -> false
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee -> match projectee with | PTuple _0 -> _0
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PRecord _0 -> true | uu____3628 -> false
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee -> match projectee with | PRecord _0 -> _0
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PConstant _0 -> true | uu____3673 -> false
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee -> match projectee with | PConstant _0 -> _0
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt8 -> true | uu____3706 -> false
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt16 -> true | uu____3717 -> false
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt32 -> true | uu____3728 -> false
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt64 -> true | uu____3739 -> false
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu____3750 -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu____3761 -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu____3772 -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu____3783 -> false
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee -> match projectee with | Bool -> true | uu____3794 -> false
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee -> match projectee with | CInt -> true | uu____3805 -> false
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee -> match projectee with | { name; typ; mut;_} -> name
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee -> match projectee with | { name; typ; mut;_} -> typ
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee -> match projectee with | { name; typ; mut;_} -> mut
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TInt _0 -> true | uu____3854 -> false
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee -> match projectee with | TInt _0 -> _0
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBuf _0 -> true | uu____3873 -> false
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee -> match projectee with | TBuf _0 -> _0
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee -> match projectee with | TUnit -> true | uu____3891 -> false
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TQualified _0 -> true | uu____3911 -> false
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | TQualified _0 -> _0
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBool -> true | uu____3953 -> false
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee -> match projectee with | TAny -> true | uu____3964 -> false
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TArrow _0 -> true | uu____3980 -> false
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee -> match projectee with | TArrow _0 -> _0
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBound _0 -> true | uu____4012 -> false
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee -> match projectee with | TBound _0 -> _0
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TApp _0 -> true | uu____4048 -> false
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee -> match projectee with | TApp _0 -> _0
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TTuple _0 -> true | uu____4111 -> false
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee -> match projectee with | TTuple _0 -> _0
let (uu___is_TConstBuf : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TConstBuf _0 -> true | uu____4136 -> false
let (__proj__TConstBuf__item___0 : typ -> typ) =
  fun projectee -> match projectee with | TConstBuf _0 -> _0
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
  =
  fun uu____4244 -> match uu____4244 with | (x, uu____4252, uu____4253) -> x
let snd3 :
  'Auu____4263 'Auu____4264 'Auu____4265 .
    ('Auu____4263 * 'Auu____4264 * 'Auu____4265) -> 'Auu____4264
  =
  fun uu____4276 -> match uu____4276 with | (uu____4283, x, uu____4285) -> x
let thd3 :
  'Auu____4295 'Auu____4296 'Auu____4297 .
    ('Auu____4295 * 'Auu____4296 * 'Auu____4297) -> 'Auu____4297
  =
  fun uu____4308 -> match uu____4308 with | (uu____4315, uu____4316, x) -> x
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4326 ->
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
  fun uu___1_4348 ->
    match uu___1_4348 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4357 -> FStar_Pervasives_Native.None
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4378 ->
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
  fun op -> (mk_op op) <> FStar_Pervasives_Native.None
let (is_machine_int : Prims.string -> Prims.bool) =
  fun m -> (mk_width m) <> FStar_Pervasives_Native.None
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }
and name = {
  pretty: Prims.string }
let (__proj__Mkenv__item__names : env -> name Prims.list) =
  fun projectee ->
    match projectee with | { names; names_t; module_name;_} -> names
let (__proj__Mkenv__item__names_t : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { names; names_t; module_name;_} -> names_t
let (__proj__Mkenv__item__module_name : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { names; names_t; module_name;_} -> module_name
let (__proj__Mkname__item__pretty : name -> Prims.string) =
  fun projectee -> match projectee with | { pretty = pretty1;_} -> pretty1
let (empty : Prims.string Prims.list -> env) =
  fun module_name -> { names = []; names_t = []; module_name }
let (extend : env -> Prims.string -> env) =
  fun env ->
    fun x ->
      let uu___166_4579 = env in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___166_4579.names_t);
        module_name = (uu___166_4579.module_name)
      }
let (extend_t : env -> Prims.string -> env) =
  fun env ->
    fun x ->
      let uu___170_4593 = env in
      {
        names = (uu___170_4593.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___170_4593.module_name)
      }
let (find_name : env -> Prims.string -> name) =
  fun env ->
    fun x ->
      let uu____4608 =
        FStar_List.tryFind (fun name -> name.pretty = x) env.names in
      match uu____4608 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None ->
          failwith "internal error: name not found"
let (find : env -> Prims.string -> Prims.int) =
  fun env ->
    fun x ->
      try
        (fun uu___181_4632 ->
           match () with
           | () -> FStar_List.index (fun name -> name.pretty = x) env.names)
          ()
      with
      | uu___180_4639 ->
          let uu____4641 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____4641
let (find_t : env -> Prims.string -> Prims.int) =
  fun env ->
    fun x ->
      try
        (fun uu___190_4661 ->
           match () with
           | () -> FStar_List.index (fun name -> name = x) env.names_t) ()
      with
      | uu___189_4670 ->
          let uu____4672 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____4672
let add_binders :
  'Auu____4683 . env -> (Prims.string * 'Auu____4683) Prims.list -> env =
  fun env ->
    fun binders ->
      FStar_List.fold_left
        (fun env1 ->
           fun uu____4718 ->
             match uu____4718 with | (name, uu____4725) -> extend env1 name)
        env binders
let (list_elements :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list)
  =
  fun e2 ->
    let rec list_elements acc e21 =
      match e21.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_CTor
          (("Prims"::[], "Cons"), hd1::tl1::[]) ->
          list_elements (hd1 :: acc) tl1
      | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[], "Nil"), []) ->
          FStar_List.rev acc
      | uu____4777 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!" in
    list_elements [] e2
let rec (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun m ->
    let uu____5003 = m in
    match uu____5003 with
    | (module_name, modul, uu____5018) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature, decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5053 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags ->
    FStar_List.choose
      (fun uu___3_5067 ->
         match uu___3_5067 with
         | FStar_Extraction_ML_Syntax.Private ->
             FStar_Pervasives_Native.Some Private
         | FStar_Extraction_ML_Syntax.NoExtract ->
             FStar_Pervasives_Native.Some WipeBody
         | FStar_Extraction_ML_Syntax.CInline ->
             FStar_Pervasives_Native.Some CInline
         | FStar_Extraction_ML_Syntax.Substitute ->
             FStar_Pervasives_Native.Some Substitute
         | FStar_Extraction_ML_Syntax.GCType ->
             FStar_Pervasives_Native.Some GCType
         | FStar_Extraction_ML_Syntax.Comment s ->
             FStar_Pervasives_Native.Some (Comment s)
         | FStar_Extraction_ML_Syntax.StackInline ->
             FStar_Pervasives_Native.Some MustDisappear
         | FStar_Extraction_ML_Syntax.CConst s ->
             FStar_Pervasives_Native.Some (Const s)
         | FStar_Extraction_ML_Syntax.CPrologue s ->
             FStar_Pervasives_Native.Some (Prologue s)
         | FStar_Extraction_ML_Syntax.CEpilogue s ->
             FStar_Pervasives_Native.Some (Epilogue s)
         | FStar_Extraction_ML_Syntax.CAbstract ->
             FStar_Pervasives_Native.Some Abstract
         | FStar_Extraction_ML_Syntax.CIfDef ->
             FStar_Pervasives_Native.Some IfDef
         | FStar_Extraction_ML_Syntax.CMacro ->
             FStar_Pervasives_Native.Some Macro
         | FStar_Extraction_ML_Syntax.Deprecated s ->
             FStar_Pervasives_Native.Some (Deprecated s)
         | uu____5080 -> FStar_Pervasives_Native.None) flags
and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags ->
    let uu____5084 =
      FStar_List.choose
        (fun uu___4_5091 ->
           match uu___4_5091 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5098 -> FStar_Pervasives_Native.None) flags in
    match uu____5084 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5111 -> FStar_Pervasives_Native.None
and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env ->
    fun d ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5125 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5127 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____5132) ->
          (FStar_Util.print1_warning
             "Not extracting exception %s to KreMLin (exceptions unsupported)\n"
             m;
           [])
and (translate_let :
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun flavor ->
      fun lb ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5159;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5162;_} when
            FStar_Util.for_some
              (fun uu___5_5167 ->
                 match uu___5_5167 with
                 | FStar_Extraction_ML_Syntax.Assumed -> true
                 | uu____5170 -> false) meta
            ->
            let name1 = ((env.module_name), name) in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args, uu____5193) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5215 -> [] in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____5223 =
                let uu____5224 =
                  let uu____5250 = translate_cc meta in
                  let uu____5253 = translate_flags meta in
                  let uu____5256 = translate_type env t0 in
                  (uu____5250, uu____5253, name1, uu____5256, arg_names) in
                DExternal uu____5224 in
              FStar_Pervasives_Native.Some uu____5223
            else
              ((let uu____5275 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5275);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5281;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args, body);
                FStar_Extraction_ML_Syntax.mlty = uu____5284;
                FStar_Extraction_ML_Syntax.loc = uu____5285;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5287;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let env1 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env name
                 else env in
               let env2 =
                 FStar_List.fold_left
                   (fun env2 -> fun name1 -> extend_t env2 name1) env1 tvars in
               let rec find_return_type eff i uu___6_5344 =
                 match uu___6_5344 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5353, eff1, t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t) in
               let name1 = ((env2.module_name), name) in
               let uu____5373 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0 in
               match uu____5373 with
               | (i, eff, t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction" in
                       let uu____5399 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5399 msg)
                    else ();
                    (let t1 = translate_type env2 t in
                     let binders = translate_binders env2 args in
                     let env3 = add_binders env2 args in
                     let cc = translate_cc meta in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST, uu____5417) ->
                           let uu____5418 = translate_flags meta in
                           MustDisappear :: uu____5418
                       | (FStar_Extraction_ML_Syntax.E_PURE, TUnit) ->
                           let uu____5421 = translate_flags meta in
                           MustDisappear :: uu____5421
                       | uu____5424 -> translate_flags meta in
                     try
                       (fun uu___364_5433 ->
                          match () with
                          | () ->
                              let body1 = translate_expr env3 body in
                              FStar_Pervasives_Native.Some
                                (DFunction
                                   (cc, meta1, (FStar_List.length tvars), t1,
                                     name1, binders, body1))) ()
                     with
                     | e ->
                         let msg = FStar_Util.print_exn e in
                         ((let uu____5465 =
                             let uu____5471 =
                               let uu____5473 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1 in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5473 msg in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5471) in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5465);
                          (let msg1 =
                             Prims.op_Hat
                               "This function was not extracted:\n" msg in
                           FStar_Pervasives_Native.Some
                             (DFunction
                                (cc, meta1, (FStar_List.length tvars), t1,
                                  name1, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5499;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5502;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = translate_flags meta in
               let env1 =
                 FStar_List.fold_left
                   (fun env1 -> fun name1 -> extend_t env1 name1) env tvars in
               let t1 = translate_type env1 t in
               let name1 = ((env1.module_name), name) in
               try
                 (fun uu___391_5539 ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5563 =
                       let uu____5569 =
                         let uu____5571 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                         let uu____5573 = FStar_Util.print_exn e in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5571
                           uu____5573 in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5569) in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5563);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5591;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5592;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5593;
            FStar_Extraction_ML_Syntax.print_typ = uu____5594;_} ->
            ((let uu____5601 =
                let uu____5607 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5607) in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5601);
             (match ts with
              | FStar_Pervasives_Native.Some (idents, t) ->
                  let uu____5614 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5614
              | FStar_Pervasives_Native.None -> ());
             FStar_Pervasives_Native.None)
and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ty ->
      let uu____5628 = ty in
      match uu____5628 with
      | (uu____5631, uu____5632, uu____5633, uu____5634, flags, uu____5636)
          ->
          if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags
          then FStar_Pervasives_Native.None
          else
            (match ty with
             | (assumed, name, _mangled_name, args, flags1,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
                 let name1 = ((env.module_name), name) in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1 -> fun name2 -> extend_t env1 name2) env args in
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
                        FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                      FStar_Util.print1_warning
                        "Not extracting type definition %s to KreMLin (assumed type)\n"
                        name2;
                      FStar_Pervasives_Native.None)
                   else
                     (let uu____5710 =
                        let uu____5711 =
                          let uu____5731 = translate_flags flags1 in
                          let uu____5734 = translate_type env1 t in
                          (name1, uu____5731, (FStar_List.length args),
                            uu____5734) in
                        DTypeAlias uu____5711 in
                      FStar_Pervasives_Native.Some uu____5710)
             | (uu____5747, name, _mangled_name, args, flags1,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name) in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1 -> fun name2 -> extend_t env1 name2) env args in
                 let uu____5792 =
                   let uu____5793 =
                     let uu____5825 = translate_flags flags1 in
                     let uu____5828 =
                       FStar_List.map
                         (fun uu____5860 ->
                            match uu____5860 with
                            | (f, t) ->
                                let uu____5880 =
                                  let uu____5886 = translate_type env1 t in
                                  (uu____5886, false) in
                                (f, uu____5880)) fields in
                     (name1, uu____5825, (FStar_List.length args),
                       uu____5828) in
                   DTypeFlat uu____5793 in
                 FStar_Pervasives_Native.Some uu____5792
             | (uu____5919, name, _mangled_name, args, flags1,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name) in
                 let flags2 = translate_flags flags1 in
                 let env1 = FStar_List.fold_left extend_t env args in
                 let uu____5969 =
                   let uu____5970 =
                     let uu____6009 =
                       FStar_List.map
                         (fun uu____6062 ->
                            match uu____6062 with
                            | (cons1, ts) ->
                                let uu____6110 =
                                  FStar_List.map
                                    (fun uu____6142 ->
                                       match uu____6142 with
                                       | (name2, t) ->
                                           let uu____6162 =
                                             let uu____6168 =
                                               translate_type env1 t in
                                             (uu____6168, false) in
                                           (name2, uu____6162)) ts in
                                (cons1, uu____6110)) branches in
                     (name1, flags2, (FStar_List.length args), uu____6009) in
                   DTypeVariant uu____5970 in
                 FStar_Pervasives_Native.Some uu____5969
             | (uu____6221, name, _mangled_name, uu____6224, uu____6225,
                uu____6226) ->
                 ((let uu____6242 =
                     let uu____6248 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6248) in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6242);
                  FStar_Pervasives_Native.None))
and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6256 = find_t env name in TBound uu____6256
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____6259, t2) ->
          let uu____6261 =
            let uu____6266 = translate_type env t1 in
            let uu____6267 = translate_type env t2 in
            (uu____6266, uu____6267) in
          TArrow uu____6261
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____6271 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6271 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____6278 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6278 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t"))
          when is_machine_int m ->
          let uu____6295 = FStar_Util.must (mk_width m) in TInt uu____6295
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t'"))
          when is_machine_int m ->
          let uu____6309 = FStar_Util.must (mk_width m) in TInt uu____6309
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu____6314 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6314 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6318::arg::uu____6320::[], p) when
          (((let uu____6326 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6326 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6331 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6331 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6336 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6336 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6341 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6341 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6345 = translate_type env arg in TBuf uu____6345
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6347::[], p) when
          ((((((((((let uu____6353 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____6353 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6358 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____6358 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6363 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____6363 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6368 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____6368 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6373 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____6373 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6378 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____6378 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6383 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____6383 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6388 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____6388 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6393 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6393 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6398 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6398 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6403 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6403 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6407 = translate_type env arg in TBuf uu____6407
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6409::uu____6410::[], p) when
          let uu____6414 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6414 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6418 = translate_type env arg in TBuf uu____6418
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu____6423 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6423 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6427 = translate_type env arg in TConstBuf uu____6427
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          (((((((((((((let uu____6434 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p in
                       uu____6434 = "FStar.Buffer.buffer") ||
                        (let uu____6439 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p in
                         uu____6439 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6444 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p in
                        uu____6444 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6449 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p in
                       uu____6449 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6454 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____6454 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6459 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____6459 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6464 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____6464 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6469 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____6469 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6474 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____6474 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6479 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____6479 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6484 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____6484 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6489 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6489 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6494 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6494 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6499 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6499 = "FStar.HyperStack.ST.mmref")
          -> let uu____6503 = translate_type env arg in TBuf uu____6503
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6504::arg::[], p) when
          (let uu____6511 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____6511 = "FStar.HyperStack.s_ref") ||
            (let uu____6516 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6516 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6520 = translate_type env arg in TBuf uu____6520
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6521::[], p) when
          let uu____6525 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6525 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6577 = FStar_List.map (translate_type env) args in
          TTuple uu____6577
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6588 =
              let uu____6603 = FStar_List.map (translate_type env) args in
              (lid, uu____6603) in
            TApp uu____6588
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6621 = FStar_List.map (translate_type env) ts in
          TTuple uu____6621
and (translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
      Prims.list -> binder Prims.list)
  = fun env -> fun args -> FStar_List.map (translate_binder env) args
and (translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) ->
      binder)
  =
  fun env ->
    fun uu____6639 ->
      match uu____6639 with
      | (name, typ) ->
          let uu____6649 = translate_type env typ in
          { name; typ = uu____6649; mut = false }
and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6656 = find env name in EBound uu____6656
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6670 =
            let uu____6675 = FStar_Util.must (mk_op op) in
            let uu____6676 = FStar_Util.must (mk_width m) in
            (uu____6675, uu____6676) in
          EOp uu____6670
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op) when
          is_bool_op op ->
          let uu____6686 =
            let uu____6691 = FStar_Util.must (mk_bool_op op) in
            (uu____6691, Bool) in
          EOp uu____6686
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,
            { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some ([], typ);
              FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
              FStar_Extraction_ML_Syntax.mllb_def = body;
              FStar_Extraction_ML_Syntax.mllb_meta = flags;
              FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),
           continuation)
          ->
          let binder =
            let uu____6714 = translate_type env typ in
            { name; typ = uu____6714; mut = false } in
          let body1 = translate_expr env body in
          let env1 = extend env name in
          let continuation1 = translate_expr env1 continuation in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) ->
          let uu____6741 =
            let uu____6752 = translate_expr env expr in
            let uu____6753 = translate_branches env branches in
            (uu____6752, uu____6753) in
          EMatch uu____6741
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6767;
                  FStar_Extraction_ML_Syntax.loc = uu____6768;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6770;
             FStar_Extraction_ML_Syntax.loc = uu____6771;_},
           arg::[])
          when
          let uu____6777 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6777 = "FStar.Dyn.undyn" ->
          let uu____6781 =
            let uu____6786 = translate_expr env arg in
            let uu____6787 = translate_type env t in (uu____6786, uu____6787) in
          ECast uu____6781
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6789;
                  FStar_Extraction_ML_Syntax.loc = uu____6790;_},
                uu____6791);
             FStar_Extraction_ML_Syntax.mlty = uu____6792;
             FStar_Extraction_ML_Syntax.loc = uu____6793;_},
           uu____6794)
          when
          let uu____6803 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6803 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6808;
                  FStar_Extraction_ML_Syntax.loc = uu____6809;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6811;
             FStar_Extraction_ML_Syntax.loc = uu____6812;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s);
             FStar_Extraction_ML_Syntax.mlty = uu____6814;
             FStar_Extraction_ML_Syntax.loc = uu____6815;_}::[])
          when
          let uu____6821 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6821 = "LowStar.Failure.failwith" ->
          let uu____6825 =
            let uu____6831 = translate_type env t in (s, uu____6831) in
          EAbortT uu____6825
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6834;
                  FStar_Extraction_ML_Syntax.loc = uu____6835;_},
                uu____6836);
             FStar_Extraction_ML_Syntax.mlty = uu____6837;
             FStar_Extraction_ML_Syntax.loc = uu____6838;_},
           arg::[])
          when
          ((let uu____6848 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____6848 = "FStar.HyperStack.All.failwith") ||
             (let uu____6853 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6853 = "FStar.Error.unexpected"))
            ||
            (let uu____6858 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6858 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6863;
               FStar_Extraction_ML_Syntax.loc = uu____6864;_} -> EAbortS msg
           | uu____6866 ->
               let print7 =
                 let uu____6868 =
                   let uu____6869 =
                     let uu____6870 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6870 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6869 in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6868 in
               let print8 =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_App (print7, [arg])) in
               let t = translate_expr env print8 in ESequence [t; EAbort])
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6877;
                  FStar_Extraction_ML_Syntax.loc = uu____6878;_},
                uu____6879);
             FStar_Extraction_ML_Syntax.mlty = uu____6880;
             FStar_Extraction_ML_Syntax.loc = uu____6881;_},
           e1::[])
          when
          (let uu____6891 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____6891 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6896 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6896 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6901;
                  FStar_Extraction_ML_Syntax.loc = uu____6902;_},
                uu____6903);
             FStar_Extraction_ML_Syntax.mlty = uu____6904;
             FStar_Extraction_ML_Syntax.loc = uu____6905;_},
           e1::e2::[])
          when
          ((((let uu____6916 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6916 = "FStar.Buffer.index") ||
               (let uu____6921 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____6921 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____6926 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6926 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____6931 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6931 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____6936 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6936 = "LowStar.ConstBuffer.index")
          ->
          let uu____6940 =
            let uu____6945 = translate_expr env e1 in
            let uu____6946 = translate_expr env e2 in
            (uu____6945, uu____6946) in
          EBufRead uu____6940
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6948;
                  FStar_Extraction_ML_Syntax.loc = uu____6949;_},
                uu____6950);
             FStar_Extraction_ML_Syntax.mlty = uu____6951;
             FStar_Extraction_ML_Syntax.loc = uu____6952;_},
           e1::[])
          when
          let uu____6960 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6960 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6964 =
            let uu____6969 = translate_expr env e1 in
            (uu____6969, (EConstant (UInt32, "0"))) in
          EBufRead uu____6964
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6973;
                  FStar_Extraction_ML_Syntax.loc = uu____6974;_},
                uu____6975);
             FStar_Extraction_ML_Syntax.mlty = uu____6976;
             FStar_Extraction_ML_Syntax.loc = uu____6977;_},
           e1::e2::[])
          when
          ((let uu____6988 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____6988 = "FStar.Buffer.create") ||
             (let uu____6993 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6993 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____6998 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6998 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7002 =
            let uu____7009 = translate_expr env e1 in
            let uu____7010 = translate_expr env e2 in
            (Stack, uu____7009, uu____7010) in
          EBufCreate uu____7002
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7012;
                  FStar_Extraction_ML_Syntax.loc = uu____7013;_},
                uu____7014);
             FStar_Extraction_ML_Syntax.mlty = uu____7015;
             FStar_Extraction_ML_Syntax.loc = uu____7016;_},
           elen::[])
          when
          let uu____7024 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7024 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7028 =
            let uu____7033 = translate_expr env elen in (Stack, uu____7033) in
          EBufCreateNoInit uu____7028
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7035;
                  FStar_Extraction_ML_Syntax.loc = uu____7036;_},
                uu____7037);
             FStar_Extraction_ML_Syntax.mlty = uu____7038;
             FStar_Extraction_ML_Syntax.loc = uu____7039;_},
           init1::[])
          when
          let uu____7047 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7047 = "FStar.HyperStack.ST.salloc" ->
          let uu____7051 =
            let uu____7058 = translate_expr env init1 in
            (Stack, uu____7058, (EConstant (UInt32, "1"))) in
          EBufCreate uu____7051
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7062;
                  FStar_Extraction_ML_Syntax.loc = uu____7063;_},
                uu____7064);
             FStar_Extraction_ML_Syntax.mlty = uu____7065;
             FStar_Extraction_ML_Syntax.loc = uu____7066;_},
           e2::[])
          when
          ((let uu____7076 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____7076 = "FStar.Buffer.createL") ||
             (let uu____7081 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7081 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7086 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7086 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7090 =
            let uu____7097 =
              let uu____7100 = list_elements e2 in
              FStar_List.map (translate_expr env) uu____7100 in
            (Stack, uu____7097) in
          EBufCreateL uu____7090
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7106;
                  FStar_Extraction_ML_Syntax.loc = uu____7107;_},
                uu____7108);
             FStar_Extraction_ML_Syntax.mlty = uu____7109;
             FStar_Extraction_ML_Syntax.loc = uu____7110;_},
           _erid::e2::[])
          when
          (let uu____7121 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____7121 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7126 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7126 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7130 =
            let uu____7137 =
              let uu____7140 = list_elements e2 in
              FStar_List.map (translate_expr env) uu____7140 in
            (Eternal, uu____7137) in
          EBufCreateL uu____7130
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7146;
                  FStar_Extraction_ML_Syntax.loc = uu____7147;_},
                uu____7148);
             FStar_Extraction_ML_Syntax.mlty = uu____7149;
             FStar_Extraction_ML_Syntax.loc = uu____7150;_},
           _rid::init1::[])
          when
          (let uu____7161 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____7161 = "FStar.HyperStack.ST.ralloc") ||
            (let uu____7166 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7166 = "FStar.HyperStack.ST.ralloc_drgn")
          ->
          let uu____7170 =
            let uu____7177 = translate_expr env init1 in
            (Eternal, uu____7177, (EConstant (UInt32, "1"))) in
          EBufCreate uu____7170
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7181;
                  FStar_Extraction_ML_Syntax.loc = uu____7182;_},
                uu____7183);
             FStar_Extraction_ML_Syntax.mlty = uu____7184;
             FStar_Extraction_ML_Syntax.loc = uu____7185;_},
           _e0::e1::e2::[])
          when
          ((let uu____7197 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____7197 = "FStar.Buffer.rcreate") ||
             (let uu____7202 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7202 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7207 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7207 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7211 =
            let uu____7218 = translate_expr env e1 in
            let uu____7219 = translate_expr env e2 in
            (Eternal, uu____7218, uu____7219) in
          EBufCreate uu____7211
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7221;
                  FStar_Extraction_ML_Syntax.loc = uu____7222;_},
                uu____7223);
             FStar_Extraction_ML_Syntax.mlty = uu____7224;
             FStar_Extraction_ML_Syntax.loc = uu____7225;_},
           uu____7226)
          when
          (((((let uu____7237 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____7237 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7242 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____7242 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7247 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____7247 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7252 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____7252 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7257 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7257 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7262 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7262 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7268;
                  FStar_Extraction_ML_Syntax.loc = uu____7269;_},
                uu____7270);
             FStar_Extraction_ML_Syntax.mlty = uu____7271;
             FStar_Extraction_ML_Syntax.loc = uu____7272;_},
           _erid::elen::[])
          when
          let uu____7281 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7281 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7285 =
            let uu____7290 = translate_expr env elen in (Eternal, uu____7290) in
          EBufCreateNoInit uu____7285
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7292;
                  FStar_Extraction_ML_Syntax.loc = uu____7293;_},
                uu____7294);
             FStar_Extraction_ML_Syntax.mlty = uu____7295;
             FStar_Extraction_ML_Syntax.loc = uu____7296;_},
           _rid::init1::[])
          when
          (let uu____7307 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____7307 = "FStar.HyperStack.ST.ralloc_mm") ||
            (let uu____7312 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7312 = "FStar.HyperStack.ST.ralloc_drgn_mm")
          ->
          let uu____7316 =
            let uu____7323 = translate_expr env init1 in
            (ManuallyManaged, uu____7323, (EConstant (UInt32, "1"))) in
          EBufCreate uu____7316
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7327;
                  FStar_Extraction_ML_Syntax.loc = uu____7328;_},
                uu____7329);
             FStar_Extraction_ML_Syntax.mlty = uu____7330;
             FStar_Extraction_ML_Syntax.loc = uu____7331;_},
           _e0::e1::e2::[])
          when
          (((let uu____7343 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7343 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7348 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____7348 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7353 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7353 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7358 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7358 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7362 =
            let uu____7369 = translate_expr env e1 in
            let uu____7370 = translate_expr env e2 in
            (ManuallyManaged, uu____7369, uu____7370) in
          EBufCreate uu____7362
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7372;
                  FStar_Extraction_ML_Syntax.loc = uu____7373;_},
                uu____7374);
             FStar_Extraction_ML_Syntax.mlty = uu____7375;
             FStar_Extraction_ML_Syntax.loc = uu____7376;_},
           _erid::elen::[])
          when
          let uu____7385 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7385 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7389 =
            let uu____7394 = translate_expr env elen in
            (ManuallyManaged, uu____7394) in
          EBufCreateNoInit uu____7389
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7396;
                  FStar_Extraction_ML_Syntax.loc = uu____7397;_},
                uu____7398);
             FStar_Extraction_ML_Syntax.mlty = uu____7399;
             FStar_Extraction_ML_Syntax.loc = uu____7400;_},
           e2::[])
          when
          let uu____7408 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7408 = "FStar.HyperStack.ST.rfree" ->
          let uu____7412 = translate_expr env e2 in EBufFree uu____7412
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7414;
                  FStar_Extraction_ML_Syntax.loc = uu____7415;_},
                uu____7416);
             FStar_Extraction_ML_Syntax.mlty = uu____7417;
             FStar_Extraction_ML_Syntax.loc = uu____7418;_},
           e2::[])
          when
          (let uu____7428 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____7428 = "FStar.Buffer.rfree") ||
            (let uu____7433 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7433 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7437 = translate_expr env e2 in EBufFree uu____7437
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7439;
                  FStar_Extraction_ML_Syntax.loc = uu____7440;_},
                uu____7441);
             FStar_Extraction_ML_Syntax.mlty = uu____7442;
             FStar_Extraction_ML_Syntax.loc = uu____7443;_},
           e1::e2::_e3::[])
          when
          let uu____7453 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7453 = "FStar.Buffer.sub" ->
          let uu____7457 =
            let uu____7462 = translate_expr env e1 in
            let uu____7463 = translate_expr env e2 in
            (uu____7462, uu____7463) in
          EBufSub uu____7457
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7465;
                  FStar_Extraction_ML_Syntax.loc = uu____7466;_},
                uu____7467);
             FStar_Extraction_ML_Syntax.mlty = uu____7468;
             FStar_Extraction_ML_Syntax.loc = uu____7469;_},
           e1::e2::_e3::[])
          when
          (let uu____7481 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____7481 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7486 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7486 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7490 =
            let uu____7495 = translate_expr env e1 in
            let uu____7496 = translate_expr env e2 in
            (uu____7495, uu____7496) in
          EBufSub uu____7490
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7498;
                  FStar_Extraction_ML_Syntax.loc = uu____7499;_},
                uu____7500);
             FStar_Extraction_ML_Syntax.mlty = uu____7501;
             FStar_Extraction_ML_Syntax.loc = uu____7502;_},
           e1::e2::[])
          when
          let uu____7511 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7511 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7516;
                  FStar_Extraction_ML_Syntax.loc = uu____7517;_},
                uu____7518);
             FStar_Extraction_ML_Syntax.mlty = uu____7519;
             FStar_Extraction_ML_Syntax.loc = uu____7520;_},
           e1::e2::[])
          when
          let uu____7529 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7529 = "FStar.Buffer.offset" ->
          let uu____7533 =
            let uu____7538 = translate_expr env e1 in
            let uu____7539 = translate_expr env e2 in
            (uu____7538, uu____7539) in
          EBufSub uu____7533
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7541;
                  FStar_Extraction_ML_Syntax.loc = uu____7542;_},
                uu____7543);
             FStar_Extraction_ML_Syntax.mlty = uu____7544;
             FStar_Extraction_ML_Syntax.loc = uu____7545;_},
           e1::e2::[])
          when
          let uu____7554 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7554 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7558 =
            let uu____7563 = translate_expr env e1 in
            let uu____7564 = translate_expr env e2 in
            (uu____7563, uu____7564) in
          EBufSub uu____7558
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7566;
                  FStar_Extraction_ML_Syntax.loc = uu____7567;_},
                uu____7568);
             FStar_Extraction_ML_Syntax.mlty = uu____7569;
             FStar_Extraction_ML_Syntax.loc = uu____7570;_},
           e1::e2::e3::[])
          when
          (((let uu____7582 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7582 = "FStar.Buffer.upd") ||
              (let uu____7587 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____7587 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7592 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7592 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7597 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7597 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7601 =
            let uu____7608 = translate_expr env e1 in
            let uu____7609 = translate_expr env e2 in
            let uu____7610 = translate_expr env e3 in
            (uu____7608, uu____7609, uu____7610) in
          EBufWrite uu____7601
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7612;
                  FStar_Extraction_ML_Syntax.loc = uu____7613;_},
                uu____7614);
             FStar_Extraction_ML_Syntax.mlty = uu____7615;
             FStar_Extraction_ML_Syntax.loc = uu____7616;_},
           e1::e2::[])
          when
          let uu____7625 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7625 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7629 =
            let uu____7636 = translate_expr env e1 in
            let uu____7637 = translate_expr env e2 in
            (uu____7636, (EConstant (UInt32, "0")), uu____7637) in
          EBufWrite uu____7629
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7641;
             FStar_Extraction_ML_Syntax.loc = uu____7642;_},
           uu____7643::[])
          when
          let uu____7646 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7646 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7651;
             FStar_Extraction_ML_Syntax.loc = uu____7652;_},
           uu____7653::[])
          when
          let uu____7656 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7656 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7661;
                  FStar_Extraction_ML_Syntax.loc = uu____7662;_},
                uu____7663);
             FStar_Extraction_ML_Syntax.mlty = uu____7664;
             FStar_Extraction_ML_Syntax.loc = uu____7665;_},
           e1::e2::e3::e4::e5::[])
          when
          ((let uu____7679 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____7679 = "FStar.Buffer.blit") ||
             (let uu____7684 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7684 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7689 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7689 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7693 =
            let uu____7704 = translate_expr env e1 in
            let uu____7705 = translate_expr env e2 in
            let uu____7706 = translate_expr env e3 in
            let uu____7707 = translate_expr env e4 in
            let uu____7708 = translate_expr env e5 in
            (uu____7704, uu____7705, uu____7706, uu____7707, uu____7708) in
          EBufBlit uu____7693
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7710;
                  FStar_Extraction_ML_Syntax.loc = uu____7711;_},
                uu____7712);
             FStar_Extraction_ML_Syntax.mlty = uu____7713;
             FStar_Extraction_ML_Syntax.loc = uu____7714;_},
           e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7730 =
            let uu____7737 = translate_expr env e1 in
            let uu____7738 = translate_expr env e2 in
            let uu____7739 = translate_expr env e3 in
            (uu____7737, uu____7738, uu____7739) in
          EBufFill uu____7730
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7741;
             FStar_Extraction_ML_Syntax.loc = uu____7742;_},
           uu____7743::[])
          when
          let uu____7746 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7746 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7751;
                  FStar_Extraction_ML_Syntax.loc = uu____7752;_},
                uu____7753);
             FStar_Extraction_ML_Syntax.mlty = uu____7754;
             FStar_Extraction_ML_Syntax.loc = uu____7755;_},
           _rid::[])
          when
          (let uu____7765 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____7765 = "FStar.HyperStack.ST.free_drgn") ||
            (let uu____7770 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7770 = "FStar.HyperStack.ST.new_drgn")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7775;
                  FStar_Extraction_ML_Syntax.loc = uu____7776;_},
                uu____7777);
             FStar_Extraction_ML_Syntax.mlty = uu____7778;
             FStar_Extraction_ML_Syntax.loc = uu____7779;_},
           _ebuf::_eseq::[])
          when
          (((let uu____7790 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7790 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7795 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____7795 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7800 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7800 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7805 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7805 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7810;
                  FStar_Extraction_ML_Syntax.loc = uu____7811;_},
                uu____7812);
             FStar_Extraction_ML_Syntax.mlty = uu____7813;
             FStar_Extraction_ML_Syntax.loc = uu____7814;_},
           e1::[])
          when
          (let uu____7824 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____7824 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu____7829 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7829 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7834;
                  FStar_Extraction_ML_Syntax.loc = uu____7835;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7837;
             FStar_Extraction_ML_Syntax.loc = uu____7838;_},
           _eqal::e1::[])
          when
          let uu____7845 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7845 = "LowStar.ConstBuffer.of_qbuf" ->
          let uu____7849 =
            let uu____7854 = translate_expr env e1 in
            let uu____7855 =
              let uu____7856 = translate_type env t in TConstBuf uu____7856 in
            (uu____7854, uu____7855) in
          ECast uu____7849
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7858;
                  FStar_Extraction_ML_Syntax.loc = uu____7859;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7861;
             FStar_Extraction_ML_Syntax.loc = uu____7862;_},
           e1::[])
          when
          ((let uu____7870 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____7870 = "LowStar.ConstBuffer.cast") ||
             (let uu____7875 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7875 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7880 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7880 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu____7884 =
            let uu____7889 = translate_expr env e1 in
            let uu____7890 =
              let uu____7891 = translate_type env t in TBuf uu____7891 in
            (uu____7889, uu____7890) in
          ECast uu____7884
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7893;
             FStar_Extraction_ML_Syntax.loc = uu____7894;_},
           e1::[])
          when
          let uu____7898 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7898 = "Obj.repr" ->
          let uu____7902 =
            let uu____7907 = translate_expr env e1 in (uu____7907, TAny) in
          ECast uu____7902
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op);
             FStar_Extraction_ML_Syntax.mlty = uu____7910;
             FStar_Extraction_ML_Syntax.loc = uu____7911;_},
           args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7927 = FStar_Util.must (mk_width m) in
          let uu____7928 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____7927 uu____7928 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op);
             FStar_Extraction_ML_Syntax.mlty = uu____7930;
             FStar_Extraction_ML_Syntax.loc = uu____7931;_},
           args)
          when is_bool_op op ->
          let uu____7945 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____7945 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7947;
             FStar_Extraction_ML_Syntax.loc = uu____7948;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____7950;
             FStar_Extraction_ML_Syntax.loc = uu____7951;_}::[])
          when is_machine_int m ->
          let uu____7976 =
            let uu____7982 = FStar_Util.must (mk_width m) in (uu____7982, c) in
          EConstant uu____7976
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7985;
             FStar_Extraction_ML_Syntax.loc = uu____7986;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____7988;
             FStar_Extraction_ML_Syntax.loc = uu____7989;_}::[])
          when is_machine_int m ->
          let uu____8014 =
            let uu____8020 = FStar_Util.must (mk_width m) in (uu____8020, c) in
          EConstant uu____8014
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[], "string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8022;
             FStar_Extraction_ML_Syntax.loc = uu____8023;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____8025;
             FStar_Extraction_ML_Syntax.loc = uu____8026;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8039 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8041;
             FStar_Extraction_ML_Syntax.loc = uu____8042;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____8044;
             FStar_Extraction_ML_Syntax.loc = uu____8045;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8062 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8064;
             FStar_Extraction_ML_Syntax.loc = uu____8065;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____8067;
             FStar_Extraction_ML_Syntax.loc = uu____8068;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8083 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[], "buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8085;
             FStar_Extraction_ML_Syntax.loc = uu____8086;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____8088;
             FStar_Extraction_ML_Syntax.loc = uu____8089;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8104 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[], c);
             FStar_Extraction_ML_Syntax.mlty = uu____8107;
             FStar_Extraction_ML_Syntax.loc = uu____8108;_},
           arg::[])
          ->
          let is_known_type =
            (((((((FStar_Util.starts_with c "uint8") ||
                    (FStar_Util.starts_with c "uint16"))
                   || (FStar_Util.starts_with c "uint32"))
                  || (FStar_Util.starts_with c "uint64"))
                 || (FStar_Util.starts_with c "int8"))
                || (FStar_Util.starts_with c "int16"))
               || (FStar_Util.starts_with c "int32"))
              || (FStar_Util.starts_with c "int64") in
          if (FStar_Util.ends_with c "uint64") && is_known_type
          then
            let uu____8136 =
              let uu____8141 = translate_expr env arg in
              (uu____8141, (TInt UInt64)) in
            ECast uu____8136
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8146 =
                 let uu____8151 = translate_expr env arg in
                 (uu____8151, (TInt UInt32)) in
               ECast uu____8146)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8156 =
                   let uu____8161 = translate_expr env arg in
                   (uu____8161, (TInt UInt16)) in
                 ECast uu____8156)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8166 =
                     let uu____8171 = translate_expr env arg in
                     (uu____8171, (TInt UInt8)) in
                   ECast uu____8166)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8176 =
                       let uu____8181 = translate_expr env arg in
                       (uu____8181, (TInt Int64)) in
                     ECast uu____8176)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8186 =
                         let uu____8191 = translate_expr env arg in
                         (uu____8191, (TInt Int32)) in
                       ECast uu____8186)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8196 =
                           let uu____8201 = translate_expr env arg in
                           (uu____8201, (TInt Int16)) in
                         ECast uu____8196)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8206 =
                             let uu____8211 = translate_expr env arg in
                             (uu____8211, (TInt Int8)) in
                           ECast uu____8206)
                        else
                          (let uu____8214 =
                             let uu____8221 =
                               let uu____8224 = translate_expr env arg in
                               [uu____8224] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8221) in
                           EApp uu____8214)
      | FStar_Extraction_ML_Syntax.MLE_App (head1, args) ->
          let uu____8244 =
            let uu____8251 = translate_expr env head1 in
            let uu____8252 = FStar_List.map (translate_expr env) args in
            (uu____8251, uu____8252) in
          EApp uu____8244
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) ->
          let uu____8263 =
            let uu____8270 = translate_expr env head1 in
            let uu____8271 = FStar_List.map (translate_type env) ty_args in
            (uu____8270, uu____8271) in
          ETypApp uu____8263
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) ->
          let uu____8279 =
            let uu____8284 = translate_expr env e1 in
            let uu____8285 = translate_type env t_to in
            (uu____8284, uu____8285) in
          ECast uu____8279
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8286, fields) ->
          let uu____8308 =
            let uu____8320 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____8321 =
              FStar_List.map
                (fun uu____8343 ->
                   match uu____8343 with
                   | (field, expr) ->
                       let uu____8358 = translate_expr env expr in
                       (field, uu____8358)) fields in
            (uu____8320, uu____8321) in
          EFlat uu____8308
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) ->
          let uu____8369 =
            let uu____8377 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____8378 = translate_expr env e1 in
            (uu____8377, uu____8378, (FStar_Pervasives_Native.snd path)) in
          EField uu____8369
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8384 ->
          let uu____8395 =
            let uu____8397 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") e in
            FStar_Util.format1 "todo: translate_expr [MLE_Let] (expr is: %s)"
              uu____8397 in
          failwith uu____8395
      | FStar_Extraction_ML_Syntax.MLE_App (head1, uu____8407) ->
          let uu____8412 =
            let uu____8414 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8414 in
          failwith uu____8412
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8426 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____8426
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8432 = FStar_List.map (translate_expr env) es in
          ETuple uu____8432
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8435, cons1), es) ->
          let uu____8450 =
            let uu____8460 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____8461 = FStar_List.map (translate_expr env) es in
            (uu____8460, cons1, uu____8461) in
          ECons uu____8450
      | FStar_Extraction_ML_Syntax.MLE_Fun (args, body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____8487 =
            let uu____8496 = translate_expr env1 body in
            let uu____8497 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____8496, uu____8497) in
          EFun uu____8487
      | FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) ->
          let uu____8507 =
            let uu____8514 = translate_expr env e1 in
            let uu____8515 = translate_expr env e2 in
            let uu____8516 =
              match e3 with
              | FStar_Pervasives_Native.None -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____8514, uu____8515, uu____8516) in
          EIfThenElse uu____8507
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8518 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8526 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8542 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8560 =
              let uu____8575 = FStar_List.map (translate_type env) ts in
              (lid, uu____8575) in
            TApp uu____8560
          else TQualified lid
      | uu____8590 ->
          let uu____8591 =
            let uu____8593 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8593 in
          failwith uu____8591
and (translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)
      Prims.list -> (pattern * expr) Prims.list)
  = fun env -> fun branches -> FStar_List.map (translate_branch env) branches
and (translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) ->
      (pattern * expr))
  =
  fun env ->
    fun uu____8627 ->
      match uu____8627 with
      | (pat, guard, expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8654 = translate_pat env pat in
            (match uu____8654 with
             | (env1, pat1) ->
                 let uu____8665 = translate_expr env1 expr in
                 (pat1, uu____8665))
          else failwith "todo: translate_branch"
and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8673 ->
    match uu___7_8673 with
    | FStar_Pervasives_Native.None -> CInt
    | FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int8) ->
        Int8
    | FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int16) ->
        Int16
    | FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32) ->
        Int32
    | FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64) ->
        Int64
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int8)
        -> UInt8
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int16)
        -> UInt16
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int32)
        -> UInt32
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int64)
        -> UInt64
and (translate_pat :
  env -> FStar_Extraction_ML_Syntax.mlpattern -> (env * pattern)) =
  fun env ->
    fun p ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Int (s, sw)) ->
          let uu____8740 =
            let uu____8741 =
              let uu____8747 = translate_width sw in (uu____8747, s) in
            PConstant uu____8741 in
          (env, uu____8740)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild ->
          let env1 = extend env "_" in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8757, cons1), ps) ->
          let uu____8772 =
            FStar_List.fold_left
              (fun uu____8792 ->
                 fun p1 ->
                   match uu____8792 with
                   | (env1, acc) ->
                       let uu____8812 = translate_pat env1 p1 in
                       (match uu____8812 with
                        | (env2, p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____8772 with
           | (env1, ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8842, ps) ->
          let uu____8864 =
            FStar_List.fold_left
              (fun uu____8901 ->
                 fun uu____8902 ->
                   match (uu____8901, uu____8902) with
                   | ((env1, acc), (field, p1)) ->
                       let uu____8982 = translate_pat env1 p1 in
                       (match uu____8982 with
                        | (env2, p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____8864 with
           | (env1, ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____9053 =
            FStar_List.fold_left
              (fun uu____9073 ->
                 fun p1 ->
                   match uu____9073 with
                   | (env1, acc) ->
                       let uu____9093 = translate_pat env1 p1 in
                       (match uu____9093 with
                        | (env2, p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____9053 with
           | (env1, ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9120 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9126 ->
          failwith "todo: translate_pat [MLP_Branch]"
and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9140 =
            let uu____9142 = FStar_String.list_of_string s in
            FStar_All.pipe_right uu____9142
              (FStar_Util.for_some
                 (fun c1 -> c1 = (FStar_Char.char_of_int Prims.int_zero))) in
          if uu____9140
          then
            let uu____9157 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu____9157
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1 in
        let s = FStar_Util.string_of_int i in
        let c2 = EConstant (UInt32, s) in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int") in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some uu____9184) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9202 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9204 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) ->
        EConstant (CInt, s)
and (mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr)
  =
  fun env ->
    fun w ->
      fun op ->
        fun args ->
          let uu____9228 =
            let uu____9235 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____9235) in
          EApp uu____9228
let (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____9247 ->
    match uu____9247 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m ->
             let m_name =
               let uu____9296 = m in
               match uu____9296 with
               | (path, uu____9311, uu____9312) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path in
             try
               (fun uu___1615_9330 ->
                  match () with
                  | () ->
                      ((let uu____9334 =
                          let uu____9336 = FStar_Options.silent () in
                          Prims.op_Negation uu____9336 in
                        if uu____9334
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____9342 = translate_module m in
                        FStar_Pervasives_Native.Some uu____9342))) ()
             with
             | uu___1614_9345 ->
                 ((let uu____9349 = FStar_Util.print_exn uu___1614_9345 in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____9349);
                  FStar_Pervasives_Native.None)) modules