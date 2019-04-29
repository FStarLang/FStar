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
  fun projectee ->
    match projectee with | DGlobal _0 -> true | uu____702 -> false
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee -> match projectee with | DGlobal _0 -> _0
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DFunction _0 -> true | uu____813 -> false
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee -> match projectee with | DFunction _0 -> _0
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeAlias _0 -> true | uu____938 -> false
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee -> match projectee with | DTypeAlias _0 -> _0
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeFlat _0 -> true | uu____1045 -> false
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee -> match projectee with | DTypeFlat _0 -> _0
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DExternal _0 -> true | uu____1177 -> false
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee -> match projectee with | DExternal _0 -> _0
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeVariant _0 -> true | uu____1294 -> false
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
    | uu____1435 -> false
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | DTypeAbstractStruct _0 -> _0
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | StdCall -> true | uu____1477 -> false
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee -> match projectee with | CDecl -> true | uu____1488 -> false
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | FastCall -> true | uu____1499 -> false
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Private -> true | uu____1510 -> false
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | WipeBody -> true | uu____1521 -> false
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CInline -> true | uu____1532 -> false
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Substitute -> true | uu____1543 -> false
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | GCType -> true | uu____1554 -> false
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Comment _0 -> true | uu____1567 -> false
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | MustDisappear -> true | uu____1588 -> false
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____1601 -> false
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Prologue _0 -> true | uu____1624 -> false
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Prologue _0 -> _0
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Epilogue _0 -> true | uu____1647 -> false
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Epilogue _0 -> _0
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Abstract -> true | uu____1668 -> false
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee -> match projectee with | IfDef -> true | uu____1679 -> false
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | Eternal -> true | uu____1690 -> false
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee -> match projectee with | Stack -> true | uu____1701 -> false
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | ManuallyManaged -> true | uu____1712 -> false
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBound _0 -> true | uu____1725 -> false
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee -> match projectee with | EBound _0 -> _0
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EQualified _0 -> true | uu____1755 -> false
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | EQualified _0 -> _0
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EConstant _0 -> true | uu____1803 -> false
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee -> match projectee with | EConstant _0 -> _0
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee -> match projectee with | EUnit -> true | uu____1836 -> false
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EApp _0 -> true | uu____1854 -> false
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee -> match projectee with | EApp _0 -> _0
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETypApp _0 -> true | uu____1897 -> false
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee -> match projectee with | ETypApp _0 -> _0
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ELet _0 -> true | uu____1940 -> false
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee -> match projectee with | ELet _0 -> _0
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EIfThenElse _0 -> true | uu____1983 -> false
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EIfThenElse _0 -> _0
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ESequence _0 -> true | uu____2022 -> false
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ESequence _0 -> _0
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAssign _0 -> true | uu____2051 -> false
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EAssign _0 -> _0
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreate _0 -> true | uu____2088 -> false
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee -> match projectee with | EBufCreate _0 -> _0
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufRead _0 -> true | uu____2129 -> false
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufRead _0 -> _0
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufWrite _0 -> true | uu____2166 -> false
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EBufWrite _0 -> _0
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufSub _0 -> true | uu____2207 -> false
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufSub _0 -> _0
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufBlit _0 -> true | uu____2248 -> false
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee -> match projectee with | EBufBlit _0 -> _0
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EMatch _0 -> true | uu____2307 -> false
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee -> match projectee with | EMatch _0 -> _0
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EOp _0 -> true | uu____2360 -> false
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee -> match projectee with | EOp _0 -> _0
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECast _0 -> true | uu____2395 -> false
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee -> match projectee with | ECast _0 -> _0
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPushFrame -> true | uu____2425 -> false
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPopFrame -> true | uu____2436 -> false
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBool _0 -> true | uu____2449 -> false
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBool _0 -> _0
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAny -> true | uu____2470 -> false
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbort -> true | uu____2481 -> false
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EReturn _0 -> true | uu____2493 -> false
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EReturn _0 -> _0
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFlat _0 -> true | uu____2523 -> false
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee -> match projectee with | EFlat _0 -> _0
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EField _0 -> true | uu____2582 -> false
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee -> match projectee with | EField _0 -> _0
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EWhile _0 -> true | uu____2626 -> false
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EWhile _0 -> _0
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateL _0 -> true | uu____2663 -> false
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee -> match projectee with | EBufCreateL _0 -> _0
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETuple _0 -> true | uu____2702 -> false
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ETuple _0 -> _0
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECons _0 -> true | uu____2736 -> false
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee -> match projectee with | ECons _0 -> _0
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFill _0 -> true | uu____2788 -> false
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EBufFill _0 -> _0
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EString _0 -> true | uu____2826 -> false
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EString _0 -> _0
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFun _0 -> true | uu____2856 -> false
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee -> match projectee with | EFun _0 -> _0
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbortS _0 -> true | uu____2900 -> false
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EAbortS _0 -> _0
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFree _0 -> true | uu____2922 -> false
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EBufFree _0 -> _0
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____2945 -> false
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee -> match projectee with | EBufCreateNoInit _0 -> _0
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu____2975 -> false
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee -> match projectee with | AddW -> true | uu____2986 -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu____2997 -> false
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee -> match projectee with | SubW -> true | uu____3008 -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu____3019 -> false
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee -> match projectee with | DivW -> true | uu____3030 -> false
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee -> match projectee with | Mult -> true | uu____3041 -> false
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee -> match projectee with | MultW -> true | uu____3052 -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu____3063 -> false
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BOr -> true | uu____3074 -> false
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BAnd -> true | uu____3085 -> false
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BXor -> true | uu____3096 -> false
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftL -> true | uu____3107 -> false
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftR -> true | uu____3118 -> false
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee -> match projectee with | BNot -> true | uu____3129 -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu____3140 -> false
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee -> match projectee with | Neq -> true | uu____3151 -> false
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu____3162 -> false
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee -> match projectee with | Lte -> true | uu____3173 -> false
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu____3184 -> false
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee -> match projectee with | Gte -> true | uu____3195 -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu____3206 -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu____3217 -> false
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee -> match projectee with | Xor -> true | uu____3228 -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu____3239 -> false
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PUnit -> true | uu____3250 -> false
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PBool _0 -> true | uu____3263 -> false
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PBool _0 -> _0
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PVar _0 -> true | uu____3285 -> false
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee -> match projectee with | PVar _0 -> _0
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PCons _0 -> true | uu____3311 -> false
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee -> match projectee with | PCons _0 -> _0
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PTuple _0 -> true | uu____3353 -> false
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee -> match projectee with | PTuple _0 -> _0
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PRecord _0 -> true | uu____3385 -> false
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee -> match projectee with | PRecord _0 -> _0
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PConstant _0 -> true | uu____3430 -> false
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee -> match projectee with | PConstant _0 -> _0
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt8 -> true | uu____3463 -> false
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt16 -> true | uu____3474 -> false
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt32 -> true | uu____3485 -> false
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt64 -> true | uu____3496 -> false
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu____3507 -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu____3518 -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu____3529 -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu____3540 -> false
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee -> match projectee with | Bool -> true | uu____3551 -> false
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee -> match projectee with | CInt -> true | uu____3562 -> false
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee -> match projectee with | { name; typ; mut;_} -> name
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee -> match projectee with | { name; typ; mut;_} -> typ
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee -> match projectee with | { name; typ; mut;_} -> mut
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TInt _0 -> true | uu____3611 -> false
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee -> match projectee with | TInt _0 -> _0
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBuf _0 -> true | uu____3630 -> false
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee -> match projectee with | TBuf _0 -> _0
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee -> match projectee with | TUnit -> true | uu____3648 -> false
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TQualified _0 -> true | uu____3668 -> false
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | TQualified _0 -> _0
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBool -> true | uu____3710 -> false
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee -> match projectee with | TAny -> true | uu____3721 -> false
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TArrow _0 -> true | uu____3737 -> false
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee -> match projectee with | TArrow _0 -> _0
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBound _0 -> true | uu____3769 -> false
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee -> match projectee with | TBound _0 -> _0
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TApp _0 -> true | uu____3805 -> false
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee -> match projectee with | TApp _0 -> _0
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TTuple _0 -> true | uu____3868 -> false
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee -> match projectee with | TTuple _0 -> _0
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
  'Auu____3969 'Auu____3970 'Auu____3971 .
    ('Auu____3969 * 'Auu____3970 * 'Auu____3971) -> 'Auu____3969
  =
  fun uu____3982 -> match uu____3982 with | (x, uu____3990, uu____3991) -> x
let snd3 :
  'Auu____4001 'Auu____4002 'Auu____4003 .
    ('Auu____4001 * 'Auu____4002 * 'Auu____4003) -> 'Auu____4002
  =
  fun uu____4014 -> match uu____4014 with | (uu____4021, x, uu____4023) -> x
let thd3 :
  'Auu____4033 'Auu____4034 'Auu____4035 .
    ('Auu____4033 * 'Auu____4034 * 'Auu____4035) -> 'Auu____4035
  =
  fun uu____4046 -> match uu____4046 with | (uu____4053, uu____4054, x) -> x
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4064 ->
    match uu___0_4064 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4076 -> FStar_Pervasives_Native.None
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4086 ->
    match uu___1_4086 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4095 -> FStar_Pervasives_Native.None
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4116 ->
    match uu___2_4116 with
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
    | uu____4161 -> FStar_Pervasives_Native.None
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
      let uu___162_4317 = env in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___162_4317.names_t);
        module_name = (uu___162_4317.module_name)
      }
let (extend_t : env -> Prims.string -> env) =
  fun env ->
    fun x ->
      let uu___166_4331 = env in
      {
        names = (uu___166_4331.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___166_4331.module_name)
      }
let (find_name : env -> Prims.string -> name) =
  fun env ->
    fun x ->
      let uu____4346 =
        FStar_List.tryFind (fun name -> name.pretty = x) env.names in
      match uu____4346 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None ->
          failwith "internal error: name not found"
let (find : env -> Prims.string -> Prims.int) =
  fun env ->
    fun x ->
      try
        (fun uu___177_4370 ->
           match () with
           | () -> FStar_List.index (fun name -> name.pretty = x) env.names)
          ()
      with
      | uu___176_4377 ->
          let uu____4379 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____4379
let (find_t : env -> Prims.string -> Prims.int) =
  fun env ->
    fun x ->
      try
        (fun uu___186_4399 ->
           match () with
           | () -> FStar_List.index (fun name -> name = x) env.names_t) ()
      with
      | uu___185_4408 ->
          let uu____4410 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____4410
let add_binders :
  'Auu____4421 . env -> (Prims.string * 'Auu____4421) Prims.list -> env =
  fun env ->
    fun binders ->
      FStar_List.fold_left
        (fun env1 ->
           fun uu____4456 ->
             match uu____4456 with | (name, uu____4463) -> extend env1 name)
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
      | uu____4515 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!" in
    list_elements [] e2
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____4734 ->
    match uu____4734 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m ->
             let m_name =
               let uu____4783 = m in
               match uu____4783 with
               | (path, uu____4798, uu____4799) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path in
             try
               (fun uu___228_4817 ->
                  match () with
                  | () ->
                      ((let uu____4821 =
                          let uu____4823 = FStar_Options.silent () in
                          Prims.op_Negation uu____4823 in
                        if uu____4821
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____4829 = translate_module m in
                        FStar_Pervasives_Native.Some uu____4829))) ()
             with
             | e ->
                 ((let uu____4838 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____4838);
                  FStar_Pervasives_Native.None)) modules
and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____4841 ->
    match uu____4841 with
    | (module_name, modul, uu____4856) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature, decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____4891 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags ->
    FStar_List.choose
      (fun uu___3_4905 ->
         match uu___3_4905 with
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
         | uu____4916 -> FStar_Pervasives_Native.None) flags
and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags ->
    let uu____4920 =
      FStar_List.choose
        (fun uu___4_4927 ->
           match uu___4_4927 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____4934 -> FStar_Pervasives_Native.None) flags in
    match uu____4920 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____4947 -> FStar_Pervasives_Native.None
and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env ->
    fun d ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____4961 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4963 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____4968) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4995;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4998;_} when
            FStar_Util.for_some
              (fun uu___5_5003 ->
                 match uu___5_5003 with
                 | FStar_Extraction_ML_Syntax.Assumed -> true
                 | uu____5006 -> false) meta
            ->
            let name1 = ((env.module_name), name) in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____5027 =
                let uu____5028 =
                  let uu____5049 = translate_cc meta in
                  let uu____5052 = translate_flags meta in
                  let uu____5055 = translate_type env t0 in
                  (uu____5049, uu____5052, name1, uu____5055) in
                DExternal uu____5028 in
              FStar_Pervasives_Native.Some uu____5027
            else
              ((let uu____5071 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5071);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5077;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args, body);
                FStar_Extraction_ML_Syntax.mlty = uu____5080;
                FStar_Extraction_ML_Syntax.loc = uu____5081;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5083;_} ->
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
               let rec find_return_type eff i uu___6_5140 =
                 match uu___6_5140 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5149, eff1, t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t) in
               let name1 = ((env2.module_name), name) in
               let uu____5169 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0 in
               match uu____5169 with
               | (i, eff, t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction" in
                       let uu____5195 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5195 msg)
                    else ();
                    (let t1 = translate_type env2 t in
                     let binders = translate_binders env2 args in
                     let env3 = add_binders env2 args in
                     let cc = translate_cc meta in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST, uu____5213) ->
                           let uu____5214 = translate_flags meta in
                           MustDisappear :: uu____5214
                       | (FStar_Extraction_ML_Syntax.E_PURE, TUnit) ->
                           let uu____5217 = translate_flags meta in
                           MustDisappear :: uu____5217
                       | uu____5220 -> translate_flags meta in
                     try
                       (fun uu___367_5229 ->
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
                         ((let uu____5261 =
                             let uu____5267 =
                               let uu____5269 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1 in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5269 msg in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5267) in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5261);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5295;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5298;_} ->
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
                 (fun uu___394_5335 ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5359 =
                       let uu____5365 =
                         let uu____5367 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                         let uu____5369 = FStar_Util.print_exn e in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5367
                           uu____5369 in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5365) in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5359);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5387;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5388;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5389;
            FStar_Extraction_ML_Syntax.print_typ = uu____5390;_} ->
            ((let uu____5397 =
                let uu____5403 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5403) in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5397);
             (match ts with
              | FStar_Pervasives_Native.Some (idents, t) ->
                  let uu____5410 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5410
              | FStar_Pervasives_Native.None -> ());
             FStar_Pervasives_Native.None)
and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ty ->
      let uu____5424 = ty in
      match uu____5424 with
      | (uu____5427, uu____5428, uu____5429, uu____5430, flags, uu____5432)
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
                     (let uu____5506 =
                        let uu____5507 =
                          let uu____5527 = translate_flags flags1 in
                          let uu____5530 = translate_type env1 t in
                          (name1, uu____5527, (FStar_List.length args),
                            uu____5530) in
                        DTypeAlias uu____5507 in
                      FStar_Pervasives_Native.Some uu____5506)
             | (uu____5543, name, _mangled_name, args, flags1,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name) in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1 -> fun name2 -> extend_t env1 name2) env args in
                 let uu____5588 =
                   let uu____5589 =
                     let uu____5621 = translate_flags flags1 in
                     let uu____5624 =
                       FStar_List.map
                         (fun uu____5656 ->
                            match uu____5656 with
                            | (f, t) ->
                                let uu____5676 =
                                  let uu____5682 = translate_type env1 t in
                                  (uu____5682, false) in
                                (f, uu____5676)) fields in
                     (name1, uu____5621, (FStar_List.length args),
                       uu____5624) in
                   DTypeFlat uu____5589 in
                 FStar_Pervasives_Native.Some uu____5588
             | (uu____5715, name, _mangled_name, args, flags1,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name) in
                 let flags2 = translate_flags flags1 in
                 let env1 = FStar_List.fold_left extend_t env args in
                 let uu____5765 =
                   let uu____5766 =
                     let uu____5805 =
                       FStar_List.map
                         (fun uu____5858 ->
                            match uu____5858 with
                            | (cons1, ts) ->
                                let uu____5906 =
                                  FStar_List.map
                                    (fun uu____5938 ->
                                       match uu____5938 with
                                       | (name2, t) ->
                                           let uu____5958 =
                                             let uu____5964 =
                                               translate_type env1 t in
                                             (uu____5964, false) in
                                           (name2, uu____5958)) ts in
                                (cons1, uu____5906)) branches in
                     (name1, flags2, (FStar_List.length args), uu____5805) in
                   DTypeVariant uu____5766 in
                 FStar_Pervasives_Native.Some uu____5765
             | (uu____6017, name, _mangled_name, uu____6020, uu____6021,
                uu____6022) ->
                 ((let uu____6038 =
                     let uu____6044 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6044) in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6038);
                  FStar_Pervasives_Native.None))
and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6052 = find_t env name in TBound uu____6052
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____6055, t2) ->
          let uu____6057 =
            let uu____6062 = translate_type env t1 in
            let uu____6063 = translate_type env t2 in
            (uu____6062, uu____6063) in
          TArrow uu____6057
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____6067 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6067 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____6074 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6074 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t"))
          when is_machine_int m ->
          let uu____6091 = FStar_Util.must (mk_width m) in TInt uu____6091
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t'"))
          when is_machine_int m ->
          let uu____6105 = FStar_Util.must (mk_width m) in TInt uu____6105
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu____6110 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6110 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6114::arg::uu____6116::[], p) when
          (((let uu____6122 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6122 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6127 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6127 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6132 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6132 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6137 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6137 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6141 = translate_type env arg in TBuf uu____6141
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6143::[], p) when
          ((((((((((let uu____6149 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____6149 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6154 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____6154 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6159 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____6159 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6164 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____6164 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6169 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____6169 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6174 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____6174 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6179 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____6179 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6184 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____6184 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6189 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6189 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6194 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6194 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6199 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6199 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6203 = translate_type env arg in TBuf uu____6203
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6205::uu____6206::[], p) when
          let uu____6210 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6210 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6214 = translate_type env arg in TBuf uu____6214
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          (((((((((((((let uu____6221 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p in
                       uu____6221 = "FStar.Buffer.buffer") ||
                        (let uu____6226 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p in
                         uu____6226 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6231 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p in
                        uu____6231 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6236 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p in
                       uu____6236 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6241 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____6241 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6246 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____6246 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6251 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____6251 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6256 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____6256 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6261 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____6261 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6266 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____6266 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6271 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____6271 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6276 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6276 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6281 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6281 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6286 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6286 = "FStar.HyperStack.ST.mmref")
          -> let uu____6290 = translate_type env arg in TBuf uu____6290
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6291::arg::[], p) when
          (let uu____6298 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____6298 = "FStar.HyperStack.s_ref") ||
            (let uu____6303 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6303 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6307 = translate_type env arg in TBuf uu____6307
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6308::[], p) when
          let uu____6312 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6312 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6364 = FStar_List.map (translate_type env) args in
          TTuple uu____6364
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____6375 =
              let uu____6390 = FStar_List.map (translate_type env) args in
              (lid, uu____6390) in
            TApp uu____6375
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6408 = FStar_List.map (translate_type env) ts in
          TTuple uu____6408
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
    fun uu____6426 ->
      match uu____6426 with
      | (name, typ) ->
          let uu____6436 = translate_type env typ in
          { name; typ = uu____6436; mut = false }
and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6443 = find env name in EBound uu____6443
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6457 =
            let uu____6462 = FStar_Util.must (mk_op op) in
            let uu____6463 = FStar_Util.must (mk_width m) in
            (uu____6462, uu____6463) in
          EOp uu____6457
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op) when
          is_bool_op op ->
          let uu____6473 =
            let uu____6478 = FStar_Util.must (mk_bool_op op) in
            (uu____6478, Bool) in
          EOp uu____6473
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
            let uu____6501 = translate_type env typ in
            { name; typ = uu____6501; mut = false } in
          let body1 = translate_expr env body in
          let env1 = extend env name in
          let continuation1 = translate_expr env1 continuation in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) ->
          let uu____6528 =
            let uu____6539 = translate_expr env expr in
            let uu____6540 = translate_branches env branches in
            (uu____6539, uu____6540) in
          EMatch uu____6528
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6554;
                  FStar_Extraction_ML_Syntax.loc = uu____6555;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6557;
             FStar_Extraction_ML_Syntax.loc = uu____6558;_},
           arg::[])
          when
          let uu____6564 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6564 = "FStar.Dyn.undyn" ->
          let uu____6568 =
            let uu____6573 = translate_expr env arg in
            let uu____6574 = translate_type env t in (uu____6573, uu____6574) in
          ECast uu____6568
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6576;
                  FStar_Extraction_ML_Syntax.loc = uu____6577;_},
                uu____6578);
             FStar_Extraction_ML_Syntax.mlty = uu____6579;
             FStar_Extraction_ML_Syntax.loc = uu____6580;_},
           uu____6581)
          when
          let uu____6590 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6590 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6595;
                  FStar_Extraction_ML_Syntax.loc = uu____6596;_},
                uu____6597);
             FStar_Extraction_ML_Syntax.mlty = uu____6598;
             FStar_Extraction_ML_Syntax.loc = uu____6599;_},
           arg::[])
          when
          ((let uu____6609 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____6609 = "FStar.HyperStack.All.failwith") ||
             (let uu____6614 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6614 = "FStar.Error.unexpected"))
            ||
            (let uu____6619 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6619 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6624;
               FStar_Extraction_ML_Syntax.loc = uu____6625;_} -> EAbortS msg
           | uu____6627 ->
               let print7 =
                 let uu____6629 =
                   let uu____6630 =
                     let uu____6631 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6631 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6630 in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6629 in
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6638;
                  FStar_Extraction_ML_Syntax.loc = uu____6639;_},
                uu____6640);
             FStar_Extraction_ML_Syntax.mlty = uu____6641;
             FStar_Extraction_ML_Syntax.loc = uu____6642;_},
           e1::[])
          when
          (let uu____6652 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____6652 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6657 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6657 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6662;
                  FStar_Extraction_ML_Syntax.loc = uu____6663;_},
                uu____6664);
             FStar_Extraction_ML_Syntax.mlty = uu____6665;
             FStar_Extraction_ML_Syntax.loc = uu____6666;_},
           e1::e2::[])
          when
          (((let uu____6677 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6677 = "FStar.Buffer.index") ||
              (let uu____6682 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6682 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____6687 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6687 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____6692 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6692 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____6696 =
            let uu____6701 = translate_expr env e1 in
            let uu____6702 = translate_expr env e2 in
            (uu____6701, uu____6702) in
          EBufRead uu____6696
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6704;
                  FStar_Extraction_ML_Syntax.loc = uu____6705;_},
                uu____6706);
             FStar_Extraction_ML_Syntax.mlty = uu____6707;
             FStar_Extraction_ML_Syntax.loc = uu____6708;_},
           e1::[])
          when
          let uu____6716 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6716 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6720 =
            let uu____6725 = translate_expr env e1 in
            (uu____6725, (EConstant (UInt32, "0"))) in
          EBufRead uu____6720
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6729;
                  FStar_Extraction_ML_Syntax.loc = uu____6730;_},
                uu____6731);
             FStar_Extraction_ML_Syntax.mlty = uu____6732;
             FStar_Extraction_ML_Syntax.loc = uu____6733;_},
           e1::e2::[])
          when
          ((let uu____6744 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____6744 = "FStar.Buffer.create") ||
             (let uu____6749 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6749 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____6754 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6754 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____6758 =
            let uu____6765 = translate_expr env e1 in
            let uu____6766 = translate_expr env e2 in
            (Stack, uu____6765, uu____6766) in
          EBufCreate uu____6758
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6768;
                  FStar_Extraction_ML_Syntax.loc = uu____6769;_},
                uu____6770);
             FStar_Extraction_ML_Syntax.mlty = uu____6771;
             FStar_Extraction_ML_Syntax.loc = uu____6772;_},
           elen::[])
          when
          let uu____6780 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6780 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____6784 =
            let uu____6789 = translate_expr env elen in (Stack, uu____6789) in
          EBufCreateNoInit uu____6784
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6791;
                  FStar_Extraction_ML_Syntax.loc = uu____6792;_},
                uu____6793);
             FStar_Extraction_ML_Syntax.mlty = uu____6794;
             FStar_Extraction_ML_Syntax.loc = uu____6795;_},
           init1::[])
          when
          let uu____6803 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6803 = "FStar.HyperStack.ST.salloc" ->
          let uu____6807 =
            let uu____6814 = translate_expr env init1 in
            (Stack, uu____6814, (EConstant (UInt32, "1"))) in
          EBufCreate uu____6807
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6818;
                  FStar_Extraction_ML_Syntax.loc = uu____6819;_},
                uu____6820);
             FStar_Extraction_ML_Syntax.mlty = uu____6821;
             FStar_Extraction_ML_Syntax.loc = uu____6822;_},
           e2::[])
          when
          ((let uu____6832 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____6832 = "FStar.Buffer.createL") ||
             (let uu____6837 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6837 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____6842 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6842 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____6846 =
            let uu____6853 =
              let uu____6856 = list_elements e2 in
              FStar_List.map (translate_expr env) uu____6856 in
            (Stack, uu____6853) in
          EBufCreateL uu____6846
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6862;
                  FStar_Extraction_ML_Syntax.loc = uu____6863;_},
                uu____6864);
             FStar_Extraction_ML_Syntax.mlty = uu____6865;
             FStar_Extraction_ML_Syntax.loc = uu____6866;_},
           _erid::e2::[])
          when
          (let uu____6877 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____6877 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____6882 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6882 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____6886 =
            let uu____6893 =
              let uu____6896 = list_elements e2 in
              FStar_List.map (translate_expr env) uu____6896 in
            (Eternal, uu____6893) in
          EBufCreateL uu____6886
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6902;
                  FStar_Extraction_ML_Syntax.loc = uu____6903;_},
                uu____6904);
             FStar_Extraction_ML_Syntax.mlty = uu____6905;
             FStar_Extraction_ML_Syntax.loc = uu____6906;_},
           _rid::init1::[])
          when
          let uu____6915 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6915 = "FStar.HyperStack.ST.ralloc" ->
          let uu____6919 =
            let uu____6926 = translate_expr env init1 in
            (Eternal, uu____6926, (EConstant (UInt32, "1"))) in
          EBufCreate uu____6919
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6930;
                  FStar_Extraction_ML_Syntax.loc = uu____6931;_},
                uu____6932);
             FStar_Extraction_ML_Syntax.mlty = uu____6933;
             FStar_Extraction_ML_Syntax.loc = uu____6934;_},
           _e0::e1::e2::[])
          when
          ((let uu____6946 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____6946 = "FStar.Buffer.rcreate") ||
             (let uu____6951 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6951 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____6956 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6956 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____6960 =
            let uu____6967 = translate_expr env e1 in
            let uu____6968 = translate_expr env e2 in
            (Eternal, uu____6967, uu____6968) in
          EBufCreate uu____6960
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6970;
                  FStar_Extraction_ML_Syntax.loc = uu____6971;_},
                uu____6972);
             FStar_Extraction_ML_Syntax.mlty = uu____6973;
             FStar_Extraction_ML_Syntax.loc = uu____6974;_},
           _erid::elen::[])
          when
          let uu____6983 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6983 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____6987 =
            let uu____6992 = translate_expr env elen in (Eternal, uu____6992) in
          EBufCreateNoInit uu____6987
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6994;
                  FStar_Extraction_ML_Syntax.loc = uu____6995;_},
                uu____6996);
             FStar_Extraction_ML_Syntax.mlty = uu____6997;
             FStar_Extraction_ML_Syntax.loc = uu____6998;_},
           _rid::init1::[])
          when
          let uu____7007 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7007 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7011 =
            let uu____7018 = translate_expr env init1 in
            (ManuallyManaged, uu____7018, (EConstant (UInt32, "1"))) in
          EBufCreate uu____7011
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7022;
                  FStar_Extraction_ML_Syntax.loc = uu____7023;_},
                uu____7024);
             FStar_Extraction_ML_Syntax.mlty = uu____7025;
             FStar_Extraction_ML_Syntax.loc = uu____7026;_},
           _e0::e1::e2::[])
          when
          (((let uu____7038 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7038 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7043 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____7043 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7048 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7048 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7053 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7053 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7057 =
            let uu____7064 = translate_expr env e1 in
            let uu____7065 = translate_expr env e2 in
            (ManuallyManaged, uu____7064, uu____7065) in
          EBufCreate uu____7057
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7067;
                  FStar_Extraction_ML_Syntax.loc = uu____7068;_},
                uu____7069);
             FStar_Extraction_ML_Syntax.mlty = uu____7070;
             FStar_Extraction_ML_Syntax.loc = uu____7071;_},
           _erid::elen::[])
          when
          let uu____7080 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7080 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7084 =
            let uu____7089 = translate_expr env elen in
            (ManuallyManaged, uu____7089) in
          EBufCreateNoInit uu____7084
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7091;
                  FStar_Extraction_ML_Syntax.loc = uu____7092;_},
                uu____7093);
             FStar_Extraction_ML_Syntax.mlty = uu____7094;
             FStar_Extraction_ML_Syntax.loc = uu____7095;_},
           e2::[])
          when
          let uu____7103 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7103 = "FStar.HyperStack.ST.rfree" ->
          let uu____7107 = translate_expr env e2 in EBufFree uu____7107
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7109;
                  FStar_Extraction_ML_Syntax.loc = uu____7110;_},
                uu____7111);
             FStar_Extraction_ML_Syntax.mlty = uu____7112;
             FStar_Extraction_ML_Syntax.loc = uu____7113;_},
           e2::[])
          when
          (let uu____7123 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____7123 = "FStar.Buffer.rfree") ||
            (let uu____7128 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7128 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7132 = translate_expr env e2 in EBufFree uu____7132
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7134;
                  FStar_Extraction_ML_Syntax.loc = uu____7135;_},
                uu____7136);
             FStar_Extraction_ML_Syntax.mlty = uu____7137;
             FStar_Extraction_ML_Syntax.loc = uu____7138;_},
           e1::e2::_e3::[])
          when
          let uu____7148 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7148 = "FStar.Buffer.sub" ->
          let uu____7152 =
            let uu____7157 = translate_expr env e1 in
            let uu____7158 = translate_expr env e2 in
            (uu____7157, uu____7158) in
          EBufSub uu____7152
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7160;
                  FStar_Extraction_ML_Syntax.loc = uu____7161;_},
                uu____7162);
             FStar_Extraction_ML_Syntax.mlty = uu____7163;
             FStar_Extraction_ML_Syntax.loc = uu____7164;_},
           e1::e2::_e3::[])
          when
          let uu____7174 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7174 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____7178 =
            let uu____7183 = translate_expr env e1 in
            let uu____7184 = translate_expr env e2 in
            (uu____7183, uu____7184) in
          EBufSub uu____7178
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7186;
                  FStar_Extraction_ML_Syntax.loc = uu____7187;_},
                uu____7188);
             FStar_Extraction_ML_Syntax.mlty = uu____7189;
             FStar_Extraction_ML_Syntax.loc = uu____7190;_},
           e1::e2::[])
          when
          let uu____7199 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7199 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7204;
                  FStar_Extraction_ML_Syntax.loc = uu____7205;_},
                uu____7206);
             FStar_Extraction_ML_Syntax.mlty = uu____7207;
             FStar_Extraction_ML_Syntax.loc = uu____7208;_},
           e1::e2::[])
          when
          let uu____7217 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7217 = "FStar.Buffer.offset" ->
          let uu____7221 =
            let uu____7226 = translate_expr env e1 in
            let uu____7227 = translate_expr env e2 in
            (uu____7226, uu____7227) in
          EBufSub uu____7221
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7229;
                  FStar_Extraction_ML_Syntax.loc = uu____7230;_},
                uu____7231);
             FStar_Extraction_ML_Syntax.mlty = uu____7232;
             FStar_Extraction_ML_Syntax.loc = uu____7233;_},
           e1::e2::[])
          when
          let uu____7242 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7242 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7246 =
            let uu____7251 = translate_expr env e1 in
            let uu____7252 = translate_expr env e2 in
            (uu____7251, uu____7252) in
          EBufSub uu____7246
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7254;
                  FStar_Extraction_ML_Syntax.loc = uu____7255;_},
                uu____7256);
             FStar_Extraction_ML_Syntax.mlty = uu____7257;
             FStar_Extraction_ML_Syntax.loc = uu____7258;_},
           e1::e2::e3::[])
          when
          (((let uu____7270 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7270 = "FStar.Buffer.upd") ||
              (let uu____7275 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____7275 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7280 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7280 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7285 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7285 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7289 =
            let uu____7296 = translate_expr env e1 in
            let uu____7297 = translate_expr env e2 in
            let uu____7298 = translate_expr env e3 in
            (uu____7296, uu____7297, uu____7298) in
          EBufWrite uu____7289
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7300;
                  FStar_Extraction_ML_Syntax.loc = uu____7301;_},
                uu____7302);
             FStar_Extraction_ML_Syntax.mlty = uu____7303;
             FStar_Extraction_ML_Syntax.loc = uu____7304;_},
           e1::e2::[])
          when
          let uu____7313 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7313 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7317 =
            let uu____7324 = translate_expr env e1 in
            let uu____7325 = translate_expr env e2 in
            (uu____7324, (EConstant (UInt32, "0")), uu____7325) in
          EBufWrite uu____7317
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7329;
             FStar_Extraction_ML_Syntax.loc = uu____7330;_},
           uu____7331::[])
          when
          let uu____7334 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7334 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7339;
             FStar_Extraction_ML_Syntax.loc = uu____7340;_},
           uu____7341::[])
          when
          let uu____7344 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7344 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7349;
                  FStar_Extraction_ML_Syntax.loc = uu____7350;_},
                uu____7351);
             FStar_Extraction_ML_Syntax.mlty = uu____7352;
             FStar_Extraction_ML_Syntax.loc = uu____7353;_},
           e1::e2::e3::e4::e5::[])
          when
          ((let uu____7367 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____7367 = "FStar.Buffer.blit") ||
             (let uu____7372 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7372 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7377 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7377 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7381 =
            let uu____7392 = translate_expr env e1 in
            let uu____7393 = translate_expr env e2 in
            let uu____7394 = translate_expr env e3 in
            let uu____7395 = translate_expr env e4 in
            let uu____7396 = translate_expr env e5 in
            (uu____7392, uu____7393, uu____7394, uu____7395, uu____7396) in
          EBufBlit uu____7381
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7398;
                  FStar_Extraction_ML_Syntax.loc = uu____7399;_},
                uu____7400);
             FStar_Extraction_ML_Syntax.mlty = uu____7401;
             FStar_Extraction_ML_Syntax.loc = uu____7402;_},
           e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7418 =
            let uu____7425 = translate_expr env e1 in
            let uu____7426 = translate_expr env e2 in
            let uu____7427 = translate_expr env e3 in
            (uu____7425, uu____7426, uu____7427) in
          EBufFill uu____7418
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7429;
             FStar_Extraction_ML_Syntax.loc = uu____7430;_},
           uu____7431::[])
          when
          let uu____7434 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7434 = "FStar.HyperStack.ST.get" -> EUnit
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
           _ebuf::_eseq::[])
          when
          (((let uu____7454 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7454 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7459 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____7459 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7464 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____7464 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7469 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____7469 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7474;
             FStar_Extraction_ML_Syntax.loc = uu____7475;_},
           e1::[])
          when
          let uu____7479 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____7479 = "Obj.repr" ->
          let uu____7483 =
            let uu____7488 = translate_expr env e1 in (uu____7488, TAny) in
          ECast uu____7483
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op);
             FStar_Extraction_ML_Syntax.mlty = uu____7491;
             FStar_Extraction_ML_Syntax.loc = uu____7492;_},
           args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7508 = FStar_Util.must (mk_width m) in
          let uu____7509 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____7508 uu____7509 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op);
             FStar_Extraction_ML_Syntax.mlty = uu____7511;
             FStar_Extraction_ML_Syntax.loc = uu____7512;_},
           args)
          when is_bool_op op ->
          let uu____7526 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____7526 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7528;
             FStar_Extraction_ML_Syntax.loc = uu____7529;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____7531;
             FStar_Extraction_ML_Syntax.loc = uu____7532;_}::[])
          when is_machine_int m ->
          let uu____7557 =
            let uu____7563 = FStar_Util.must (mk_width m) in (uu____7563, c) in
          EConstant uu____7557
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7566;
             FStar_Extraction_ML_Syntax.loc = uu____7567;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____7569;
             FStar_Extraction_ML_Syntax.loc = uu____7570;_}::[])
          when is_machine_int m ->
          let uu____7595 =
            let uu____7601 = FStar_Util.must (mk_width m) in (uu____7601, c) in
          EConstant uu____7595
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[], "string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7603;
             FStar_Extraction_ML_Syntax.loc = uu____7604;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____7606;
             FStar_Extraction_ML_Syntax.loc = uu____7607;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7620 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7622;
             FStar_Extraction_ML_Syntax.loc = uu____7623;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____7625;
             FStar_Extraction_ML_Syntax.loc = uu____7626;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7643 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7645;
             FStar_Extraction_ML_Syntax.loc = uu____7646;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____7648;
             FStar_Extraction_ML_Syntax.loc = uu____7649;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7664 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[], "buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7666;
             FStar_Extraction_ML_Syntax.loc = uu____7667;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____7669;
             FStar_Extraction_ML_Syntax.loc = uu____7670;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____7685 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[], c);
             FStar_Extraction_ML_Syntax.mlty = uu____7688;
             FStar_Extraction_ML_Syntax.loc = uu____7689;_},
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
            let uu____7717 =
              let uu____7722 = translate_expr env arg in
              (uu____7722, (TInt UInt64)) in
            ECast uu____7717
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____7727 =
                 let uu____7732 = translate_expr env arg in
                 (uu____7732, (TInt UInt32)) in
               ECast uu____7727)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____7737 =
                   let uu____7742 = translate_expr env arg in
                   (uu____7742, (TInt UInt16)) in
                 ECast uu____7737)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____7747 =
                     let uu____7752 = translate_expr env arg in
                     (uu____7752, (TInt UInt8)) in
                   ECast uu____7747)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____7757 =
                       let uu____7762 = translate_expr env arg in
                       (uu____7762, (TInt Int64)) in
                     ECast uu____7757)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____7767 =
                         let uu____7772 = translate_expr env arg in
                         (uu____7772, (TInt Int32)) in
                       ECast uu____7767)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____7777 =
                           let uu____7782 = translate_expr env arg in
                           (uu____7782, (TInt Int16)) in
                         ECast uu____7777)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____7787 =
                             let uu____7792 = translate_expr env arg in
                             (uu____7792, (TInt Int8)) in
                           ECast uu____7787)
                        else
                          (let uu____7795 =
                             let uu____7802 =
                               let uu____7805 = translate_expr env arg in
                               [uu____7805] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____7802) in
                           EApp uu____7795)
      | FStar_Extraction_ML_Syntax.MLE_App (head1, args) ->
          let uu____7825 =
            let uu____7832 = translate_expr env head1 in
            let uu____7833 = FStar_List.map (translate_expr env) args in
            (uu____7832, uu____7833) in
          EApp uu____7825
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) ->
          let uu____7844 =
            let uu____7851 = translate_expr env head1 in
            let uu____7852 = FStar_List.map (translate_type env) ty_args in
            (uu____7851, uu____7852) in
          ETypApp uu____7844
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) ->
          let uu____7860 =
            let uu____7865 = translate_expr env e1 in
            let uu____7866 = translate_type env t_to in
            (uu____7865, uu____7866) in
          ECast uu____7860
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____7867, fields) ->
          let uu____7889 =
            let uu____7901 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____7902 =
              FStar_List.map
                (fun uu____7924 ->
                   match uu____7924 with
                   | (field, expr) ->
                       let uu____7939 = translate_expr env expr in
                       (field, uu____7939)) fields in
            (uu____7901, uu____7902) in
          EFlat uu____7889
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) ->
          let uu____7950 =
            let uu____7958 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____7959 = translate_expr env e1 in
            (uu____7958, uu____7959, (FStar_Pervasives_Native.snd path)) in
          EField uu____7950
      | FStar_Extraction_ML_Syntax.MLE_Let uu____7965 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1, uu____7978) ->
          let uu____7983 =
            let uu____7985 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____7985 in
          failwith uu____7983
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____7997 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____7997
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8003 = FStar_List.map (translate_expr env) es in
          ETuple uu____8003
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8006, cons1), es) ->
          let uu____8021 =
            let uu____8031 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____8032 = FStar_List.map (translate_expr env) es in
            (uu____8031, cons1, uu____8032) in
          ECons uu____8021
      | FStar_Extraction_ML_Syntax.MLE_Fun (args, body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____8058 =
            let uu____8067 = translate_expr env1 body in
            let uu____8068 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____8067, uu____8068) in
          EFun uu____8058
      | FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) ->
          let uu____8078 =
            let uu____8085 = translate_expr env e1 in
            let uu____8086 = translate_expr env e2 in
            let uu____8087 =
              match e3 with
              | FStar_Pervasives_Native.None -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____8085, uu____8086, uu____8087) in
          EIfThenElse uu____8078
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8089 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8097 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8113 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____8131 =
              let uu____8146 = FStar_List.map (translate_type env) ts in
              (lid, uu____8146) in
            TApp uu____8131
          else TQualified lid
      | uu____8161 ->
          let uu____8162 =
            let uu____8164 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8164 in
          failwith uu____8162
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
    fun uu____8198 ->
      match uu____8198 with
      | (pat, guard, expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8225 = translate_pat env pat in
            (match uu____8225 with
             | (env1, pat1) ->
                 let uu____8236 = translate_expr env1 expr in
                 (pat1, uu____8236))
          else failwith "todo: translate_branch"
and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8244 ->
    match uu___7_8244 with
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
          let uu____8311 =
            let uu____8312 =
              let uu____8318 = translate_width sw in (uu____8318, s) in
            PConstant uu____8312 in
          (env, uu____8311)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild ->
          let env1 = extend env "_" in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8328, cons1), ps) ->
          let uu____8343 =
            FStar_List.fold_left
              (fun uu____8363 ->
                 fun p1 ->
                   match uu____8363 with
                   | (env1, acc) ->
                       let uu____8383 = translate_pat env1 p1 in
                       (match uu____8383 with
                        | (env2, p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____8343 with
           | (env1, ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8413, ps) ->
          let uu____8435 =
            FStar_List.fold_left
              (fun uu____8472 ->
                 fun uu____8473 ->
                   match (uu____8472, uu____8473) with
                   | ((env1, acc), (field, p1)) ->
                       let uu____8553 = translate_pat env1 p1 in
                       (match uu____8553 with
                        | (env2, p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____8435 with
           | (env1, ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____8624 =
            FStar_List.fold_left
              (fun uu____8644 ->
                 fun p1 ->
                   match uu____8644 with
                   | (env1, acc) ->
                       let uu____8664 = translate_pat env1 p1 in
                       (match uu____8664 with
                        | (env2, p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____8624 with
           | (env1, ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____8691 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____8697 ->
          failwith "todo: translate_pat [MLP_Branch]"
and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____8711 =
            let uu____8713 = FStar_String.list_of_string s in
            FStar_All.pipe_right uu____8713
              (FStar_Util.for_some
                 (fun c1 ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0")))) in
          if uu____8711
          then
            let uu____8728 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu____8728
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1 in
        let s = FStar_Util.string_of_int i in
        let c2 = EConstant (UInt32, s) in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int") in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some uu____8755) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____8773 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____8775 ->
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
          let uu____8799 =
            let uu____8806 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____8806) in
          EApp uu____8799