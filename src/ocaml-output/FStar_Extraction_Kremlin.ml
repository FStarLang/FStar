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
  fun projectee -> match projectee with | DGlobal _0 -> true | uu___ -> false
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee -> match projectee with | DGlobal _0 -> _0
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DFunction _0 -> true | uu___ -> false
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee -> match projectee with | DFunction _0 -> _0
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeAlias _0 -> true | uu___ -> false
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee -> match projectee with | DTypeAlias _0 -> _0
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeFlat _0 -> true | uu___ -> false
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee -> match projectee with | DTypeFlat _0 -> _0
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu___ -> false
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeVariant _0 -> true | uu___ -> false
let (__proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list)
      Prims.list))
  = fun projectee -> match projectee with | DTypeVariant _0 -> _0
let (uu___is_DTypeAbstractStruct : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeAbstractStruct _0 -> true | uu___ -> false
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | DTypeAbstractStruct _0 -> _0
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DExternal _0 -> true | uu___ -> false
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee -> match projectee with | DExternal _0 -> _0
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee -> match projectee with | StdCall -> true | uu___ -> false
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee -> match projectee with | CDecl -> true | uu___ -> false
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee -> match projectee with | FastCall -> true | uu___ -> false
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee -> match projectee with | Private -> true | uu___ -> false
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee -> match projectee with | WipeBody -> true | uu___ -> false
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee -> match projectee with | CInline -> true | uu___ -> false
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee -> match projectee with | Substitute -> true | uu___ -> false
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee -> match projectee with | GCType -> true | uu___ -> false
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee -> match projectee with | Comment _0 -> true | uu___ -> false
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | MustDisappear -> true | uu___ -> false
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee -> match projectee with | Const _0 -> true | uu___ -> false
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Prologue _0 -> true | uu___ -> false
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Prologue _0 -> _0
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Epilogue _0 -> true | uu___ -> false
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Epilogue _0 -> _0
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee -> match projectee with | Abstract -> true | uu___ -> false
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee -> match projectee with | IfDef -> true | uu___ -> false
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee -> match projectee with | Macro -> true | uu___ -> false
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Deprecated _0 -> true | uu___ -> false
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Deprecated _0 -> _0
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee -> match projectee with | Eternal -> true | uu___ -> false
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee -> match projectee with | Stack -> true | uu___ -> false
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | ManuallyManaged -> true | uu___ -> false
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBound _0 -> true | uu___ -> false
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee -> match projectee with | EBound _0 -> _0
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EQualified _0 -> true | uu___ -> false
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | EQualified _0 -> _0
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EConstant _0 -> true | uu___ -> false
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee -> match projectee with | EConstant _0 -> _0
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee -> match projectee with | EUnit -> true | uu___ -> false
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee -> match projectee with | EApp _0 -> true | uu___ -> false
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee -> match projectee with | EApp _0 -> _0
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee -> match projectee with | ETypApp _0 -> true | uu___ -> false
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee -> match projectee with | ETypApp _0 -> _0
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee -> match projectee with | ELet _0 -> true | uu___ -> false
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee -> match projectee with | ELet _0 -> _0
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EIfThenElse _0 -> true | uu___ -> false
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EIfThenElse _0 -> _0
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ESequence _0 -> true | uu___ -> false
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ESequence _0 -> _0
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAssign _0 -> true | uu___ -> false
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EAssign _0 -> _0
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreate _0 -> true | uu___ -> false
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee -> match projectee with | EBufCreate _0 -> _0
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufRead _0 -> true | uu___ -> false
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufRead _0 -> _0
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufWrite _0 -> true | uu___ -> false
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EBufWrite _0 -> _0
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBufSub _0 -> true | uu___ -> false
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufSub _0 -> _0
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufBlit _0 -> true | uu___ -> false
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee -> match projectee with | EBufBlit _0 -> _0
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee -> match projectee with | EMatch _0 -> true | uu___ -> false
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee -> match projectee with | EMatch _0 -> _0
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee -> match projectee with | EOp _0 -> true | uu___ -> false
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee -> match projectee with | EOp _0 -> _0
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee -> match projectee with | ECast _0 -> true | uu___ -> false
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee -> match projectee with | ECast _0 -> _0
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee -> match projectee with | EPushFrame -> true | uu___ -> false
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee -> match projectee with | EPopFrame -> true | uu___ -> false
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBool _0 -> true | uu___ -> false
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBool _0 -> _0
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAny -> true | uu___ -> false
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAbort -> true | uu___ -> false
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee -> match projectee with | EReturn _0 -> true | uu___ -> false
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EReturn _0 -> _0
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee -> match projectee with | EFlat _0 -> true | uu___ -> false
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee -> match projectee with | EFlat _0 -> _0
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee -> match projectee with | EField _0 -> true | uu___ -> false
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee -> match projectee with | EField _0 -> _0
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee -> match projectee with | EWhile _0 -> true | uu___ -> false
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EWhile _0 -> _0
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateL _0 -> true | uu___ -> false
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee -> match projectee with | EBufCreateL _0 -> _0
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee -> match projectee with | ETuple _0 -> true | uu___ -> false
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ETuple _0 -> _0
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee -> match projectee with | ECons _0 -> true | uu___ -> false
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee -> match projectee with | ECons _0 -> _0
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFill _0 -> true | uu___ -> false
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EBufFill _0 -> _0
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee -> match projectee with | EString _0 -> true | uu___ -> false
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EString _0 -> _0
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee -> match projectee with | EFun _0 -> true | uu___ -> false
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee -> match projectee with | EFun _0 -> _0
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAbortS _0 -> true | uu___ -> false
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EAbortS _0 -> _0
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFree _0 -> true | uu___ -> false
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EBufFree _0 -> _0
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateNoInit _0 -> true | uu___ -> false
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee -> match projectee with | EBufCreateNoInit _0 -> _0
let (uu___is_EAbortT : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAbortT _0 -> true | uu___ -> false
let (__proj__EAbortT__item___0 : expr -> (Prims.string * typ)) =
  fun projectee -> match projectee with | EAbortT _0 -> _0
let (uu___is_EComment : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EComment _0 -> true | uu___ -> false
let (__proj__EComment__item___0 :
  expr -> (Prims.string * expr * Prims.string)) =
  fun projectee -> match projectee with | EComment _0 -> _0
let (uu___is_EStandaloneComment : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EStandaloneComment _0 -> true | uu___ -> false
let (__proj__EStandaloneComment__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EStandaloneComment _0 -> _0
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu___ -> false
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee -> match projectee with | AddW -> true | uu___ -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu___ -> false
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee -> match projectee with | SubW -> true | uu___ -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu___ -> false
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee -> match projectee with | DivW -> true | uu___ -> false
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee -> match projectee with | Mult -> true | uu___ -> false
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee -> match projectee with | MultW -> true | uu___ -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu___ -> false
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BOr -> true | uu___ -> false
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BAnd -> true | uu___ -> false
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BXor -> true | uu___ -> false
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee -> match projectee with | BShiftL -> true | uu___ -> false
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee -> match projectee with | BShiftR -> true | uu___ -> false
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee -> match projectee with | BNot -> true | uu___ -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu___ -> false
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee -> match projectee with | Neq -> true | uu___ -> false
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu___ -> false
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee -> match projectee with | Lte -> true | uu___ -> false
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu___ -> false
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee -> match projectee with | Gte -> true | uu___ -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu___ -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu___ -> false
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee -> match projectee with | Xor -> true | uu___ -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu___ -> false
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PUnit -> true | uu___ -> false
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PBool _0 -> true | uu___ -> false
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PBool _0 -> _0
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PVar _0 -> true | uu___ -> false
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee -> match projectee with | PVar _0 -> _0
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PCons _0 -> true | uu___ -> false
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee -> match projectee with | PCons _0 -> _0
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PTuple _0 -> true | uu___ -> false
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee -> match projectee with | PTuple _0 -> _0
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PRecord _0 -> true | uu___ -> false
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee -> match projectee with | PRecord _0 -> _0
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PConstant _0 -> true | uu___ -> false
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee -> match projectee with | PConstant _0 -> _0
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt8 -> true | uu___ -> false
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt16 -> true | uu___ -> false
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt32 -> true | uu___ -> false
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt64 -> true | uu___ -> false
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu___ -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu___ -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu___ -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu___ -> false
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee -> match projectee with | Bool -> true | uu___ -> false
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee -> match projectee with | CInt -> true | uu___ -> false
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee -> match projectee with | { name; typ = typ1; mut;_} -> name
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee -> match projectee with | { name; typ = typ1; mut;_} -> typ1
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee -> match projectee with | { name; typ = typ1; mut;_} -> mut
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee -> match projectee with | TInt _0 -> true | uu___ -> false
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee -> match projectee with | TInt _0 -> _0
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBuf _0 -> true | uu___ -> false
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee -> match projectee with | TBuf _0 -> _0
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee -> match projectee with | TUnit -> true | uu___ -> false
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TQualified _0 -> true | uu___ -> false
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | TQualified _0 -> _0
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBool -> true | uu___ -> false
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee -> match projectee with | TAny -> true | uu___ -> false
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee -> match projectee with | TArrow _0 -> true | uu___ -> false
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee -> match projectee with | TArrow _0 -> _0
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBound _0 -> true | uu___ -> false
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee -> match projectee with | TBound _0 -> _0
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee -> match projectee with | TApp _0 -> true | uu___ -> false
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee -> match projectee with | TApp _0 -> _0
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee -> match projectee with | TTuple _0 -> true | uu___ -> false
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee -> match projectee with | TTuple _0 -> _0
let (uu___is_TConstBuf : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TConstBuf _0 -> true | uu___ -> false
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
let fst3 : 'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu =
  fun uu___ -> match uu___ with | (x, uu___1, uu___2) -> x
let snd3 : 'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu1 =
  fun uu___ -> match uu___ with | (uu___1, x, uu___2) -> x
let thd3 : 'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu2 =
  fun uu___ -> match uu___ with | (uu___1, uu___2, x) -> x
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___ ->
    match uu___ with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu___1 -> FStar_Pervasives_Native.None
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___ ->
    match uu___ with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu___1 -> FStar_Pervasives_Native.None
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op1 -> (mk_bool_op op1) <> FStar_Pervasives_Native.None
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___ ->
    match uu___ with
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
    | uu___1 -> FStar_Pervasives_Native.None
let (is_op : Prims.string -> Prims.bool) =
  fun op1 -> (mk_op op1) <> FStar_Pervasives_Native.None
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
  fun projectee -> match projectee with | { pretty;_} -> pretty
let (empty : Prims.string Prims.list -> env) =
  fun module_name -> { names = []; names_t = []; module_name }
let (extend : env -> Prims.string -> env) =
  fun env1 ->
    fun x ->
      let uu___ = env1 in
      {
        names = ({ pretty = x } :: (env1.names));
        names_t = (uu___.names_t);
        module_name = (uu___.module_name)
      }
let (extend_t : env -> Prims.string -> env) =
  fun env1 ->
    fun x ->
      let uu___ = env1 in
      {
        names = (uu___.names);
        names_t = (x :: (env1.names_t));
        module_name = (uu___.module_name)
      }
let (find_name : env -> Prims.string -> name) =
  fun env1 ->
    fun x ->
      let uu___ =
        FStar_List.tryFind (fun name1 -> name1.pretty = x) env1.names in
      match uu___ with
      | FStar_Pervasives_Native.Some name1 -> name1
      | FStar_Pervasives_Native.None ->
          failwith "internal error: name not found"
let (find : env -> Prims.string -> Prims.int) =
  fun env1 ->
    fun x ->
      try
        (fun uu___ ->
           match () with
           | () ->
               FStar_List.index (fun name1 -> name1.pretty = x) env1.names)
          ()
      with
      | uu___ ->
          let uu___1 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu___1
let (find_t : env -> Prims.string -> Prims.int) =
  fun env1 ->
    fun x ->
      try
        (fun uu___ ->
           match () with
           | () -> FStar_List.index (fun name1 -> name1 = x) env1.names_t) ()
      with
      | uu___ ->
          let uu___1 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu___1
let add_binders : 'uuuuu . env -> (Prims.string * 'uuuuu) Prims.list -> env =
  fun env1 ->
    fun binders ->
      FStar_List.fold_left
        (fun env2 ->
           fun uu___ ->
             match uu___ with | (name1, uu___1) -> extend env2 name1) env1
        binders
let (list_elements :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list)
  =
  fun e2 ->
    let rec list_elements1 acc e21 =
      match e21.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_CTor
          (("Prims"::[], "Cons"), hd::tl::[]) ->
          list_elements1 (hd :: acc) tl
      | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[], "Nil"), []) ->
          FStar_List.rev acc
      | uu___ ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!" in
    list_elements1 [] e2
let rec (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun m ->
    let uu___ = m in
    match uu___ with
    | (module_name, modul, uu___1) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program1 =
          match modul with
          | FStar_Pervasives_Native.Some (_signature, decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu___2 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program1)
and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags ->
    FStar_List.choose
      (fun uu___ ->
         match uu___ with
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
         | uu___1 -> FStar_Pervasives_Native.None) flags
and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags ->
    let uu___ =
      FStar_List.choose
        (fun uu___1 ->
           match uu___1 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu___2 -> FStar_Pervasives_Native.None) flags in
    match uu___ with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu___1 -> FStar_Pervasives_Native.None
and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env1 ->
    fun d ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) ->
          FStar_List.choose (translate_let env1 flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu___ -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env1) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu___ ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m, uu___) ->
          (FStar_Util.print1_warning
             "Not extracting exception %s to KreMLin (exceptions unsupported)\n"
             m;
           [])
and (translate_let :
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun flavor ->
      fun lb ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu___1;_} when
            FStar_Util.for_some
              (fun uu___2 ->
                 match uu___2 with
                 | FStar_Extraction_ML_Syntax.Assumed -> true
                 | uu___3 -> false) meta
            ->
            let name2 = ((env1.module_name), name1) in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args, uu___2) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu___2 -> [] in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu___2 =
                let uu___3 =
                  let uu___4 = translate_cc meta in
                  let uu___5 = translate_flags meta in
                  let uu___6 = translate_type env1 t0 in
                  (uu___4, uu___5, name2, uu___6, arg_names) in
                DExternal uu___3 in
              FStar_Pervasives_Native.Some uu___2
            else
              ((let uu___4 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name2 in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu___4);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args, body);
                FStar_Extraction_ML_Syntax.mlty = uu___1;
                FStar_Extraction_ML_Syntax.loc = uu___2;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu___3;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let env2 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env1 name1
                 else env1 in
               let env3 =
                 FStar_List.fold_left
                   (fun env4 -> fun name2 -> extend_t env4 name2) env2 tvars in
               let rec find_return_type eff i uu___5 =
                 match uu___5 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu___6, eff1, t) when
                     i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t) in
               let name2 = ((env3.module_name), name1) in
               let uu___5 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0 in
               match uu___5 with
               | (i, eff, t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction" in
                       let uu___7 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name2 in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu___7 msg)
                    else ();
                    (let t1 = translate_type env3 t in
                     let binders = translate_binders env3 args in
                     let env4 = add_binders env3 args in
                     let cc1 = translate_cc meta in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_ERASABLE, uu___7) ->
                           let uu___8 = translate_flags meta in MustDisappear
                             :: uu___8
                       | (FStar_Extraction_ML_Syntax.E_PURE, TUnit) ->
                           let uu___7 = translate_flags meta in MustDisappear
                             :: uu___7
                       | uu___7 -> translate_flags meta in
                     try
                       (fun uu___7 ->
                          match () with
                          | () ->
                              let body1 = translate_expr env4 body in
                              FStar_Pervasives_Native.Some
                                (DFunction
                                   (cc1, meta1, (FStar_List.length tvars),
                                     t1, name2, binders, body1))) ()
                     with
                     | e ->
                         let msg = FStar_Util.print_exn e in
                         ((let uu___9 =
                             let uu___10 =
                               let uu___11 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name2 in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu___11 msg in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu___10) in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu___9);
                          (let msg1 =
                             Prims.op_Hat
                               "This function was not extracted:\n" msg in
                           FStar_Pervasives_Native.Some
                             (DFunction
                                (cc1, meta1, (FStar_List.length tvars), t1,
                                  name2, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStar_Extraction_ML_Syntax.mllb_def = expr1;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu___1;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = translate_flags meta in
               let env2 =
                 FStar_List.fold_left
                   (fun env3 -> fun name2 -> extend_t env3 name2) env1 tvars in
               let t1 = translate_type env2 t in
               let name2 = ((env2.module_name), name1) in
               try
                 (fun uu___3 ->
                    match () with
                    | () ->
                        let expr2 = translate_expr env2 expr1 in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name2, (FStar_List.length tvars), t1,
                               expr2))) ()
               with
               | e ->
                   ((let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name2 in
                         let uu___8 = FStar_Util.print_exn e in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu___7
                           uu___8 in
                       (FStar_Errors.Warning_DefinitionNotTranslated, uu___6) in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu___5);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name2, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStar_Extraction_ML_Syntax.mllb_def = uu___1;
            FStar_Extraction_ML_Syntax.mllb_meta = uu___2;
            FStar_Extraction_ML_Syntax.print_typ = uu___3;_} ->
            ((let uu___5 =
                let uu___6 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name1 in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu___6) in
              FStar_Errors.log_issue FStar_Range.dummyRange uu___5);
             (match ts with
              | FStar_Pervasives_Native.Some (idents, t) ->
                  let uu___6 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu___6
              | FStar_Pervasives_Native.None -> ());
             FStar_Pervasives_Native.None)
and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ty ->
      if
        FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract
          ty.FStar_Extraction_ML_Syntax.tydecl_meta
      then FStar_Pervasives_Native.None
      else
        (match ty with
         | { FStar_Extraction_ML_Syntax.tydecl_assumed = assumed;
             FStar_Extraction_ML_Syntax.tydecl_name = name1;
             FStar_Extraction_ML_Syntax.tydecl_ignored = uu___1;
             FStar_Extraction_ML_Syntax.tydecl_parameters = args;
             FStar_Extraction_ML_Syntax.tydecl_meta = flags;
             FStar_Extraction_ML_Syntax.tydecl_defn =
               FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.MLTD_Abbrev t);_}
             ->
             let name2 = ((env1.module_name), name1) in
             let env2 =
               FStar_List.fold_left
                 (fun env3 -> fun name3 -> extend_t env3 name3) env1 args in
             if
               assumed &&
                 (FStar_List.mem FStar_Extraction_ML_Syntax.CAbstract flags)
             then FStar_Pervasives_Native.Some (DTypeAbstractStruct name2)
             else
               if assumed
               then
                 (let name3 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath name2 in
                  FStar_Util.print1_warning
                    "Not extracting type definition %s to KreMLin (assumed type)\n"
                    name3;
                  FStar_Pervasives_Native.None)
               else
                 (let uu___4 =
                    let uu___5 =
                      let uu___6 = translate_flags flags in
                      let uu___7 = translate_type env2 t in
                      (name2, uu___6, (FStar_List.length args), uu___7) in
                    DTypeAlias uu___5 in
                  FStar_Pervasives_Native.Some uu___4)
         | { FStar_Extraction_ML_Syntax.tydecl_assumed = uu___1;
             FStar_Extraction_ML_Syntax.tydecl_name = name1;
             FStar_Extraction_ML_Syntax.tydecl_ignored = uu___2;
             FStar_Extraction_ML_Syntax.tydecl_parameters = args;
             FStar_Extraction_ML_Syntax.tydecl_meta = flags;
             FStar_Extraction_ML_Syntax.tydecl_defn =
               FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.MLTD_Record fields);_}
             ->
             let name2 = ((env1.module_name), name1) in
             let env2 =
               FStar_List.fold_left
                 (fun env3 -> fun name3 -> extend_t env3 name3) env1 args in
             let uu___3 =
               let uu___4 =
                 let uu___5 = translate_flags flags in
                 let uu___6 =
                   FStar_List.map
                     (fun uu___7 ->
                        match uu___7 with
                        | (f, t) ->
                            let uu___8 =
                              let uu___9 = translate_type env2 t in
                              (uu___9, false) in
                            (f, uu___8)) fields in
                 (name2, uu___5, (FStar_List.length args), uu___6) in
               DTypeFlat uu___4 in
             FStar_Pervasives_Native.Some uu___3
         | { FStar_Extraction_ML_Syntax.tydecl_assumed = uu___1;
             FStar_Extraction_ML_Syntax.tydecl_name = name1;
             FStar_Extraction_ML_Syntax.tydecl_ignored = uu___2;
             FStar_Extraction_ML_Syntax.tydecl_parameters = args;
             FStar_Extraction_ML_Syntax.tydecl_meta = flags;
             FStar_Extraction_ML_Syntax.tydecl_defn =
               FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.MLTD_DType branches1);_}
             ->
             let name2 = ((env1.module_name), name1) in
             let flags1 = translate_flags flags in
             let env2 = FStar_List.fold_left extend_t env1 args in
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   FStar_List.map
                     (fun uu___6 ->
                        match uu___6 with
                        | (cons, ts) ->
                            let uu___7 =
                              FStar_List.map
                                (fun uu___8 ->
                                   match uu___8 with
                                   | (name3, t) ->
                                       let uu___9 =
                                         let uu___10 = translate_type env2 t in
                                         (uu___10, false) in
                                       (name3, uu___9)) ts in
                            (cons, uu___7)) branches1 in
                 (name2, flags1, (FStar_List.length args), uu___5) in
               DTypeVariant uu___4 in
             FStar_Pervasives_Native.Some uu___3
         | { FStar_Extraction_ML_Syntax.tydecl_assumed = uu___1;
             FStar_Extraction_ML_Syntax.tydecl_name = name1;
             FStar_Extraction_ML_Syntax.tydecl_ignored = uu___2;
             FStar_Extraction_ML_Syntax.tydecl_parameters = uu___3;
             FStar_Extraction_ML_Syntax.tydecl_meta = uu___4;
             FStar_Extraction_ML_Syntax.tydecl_defn = uu___5;_} ->
             ((let uu___7 =
                 let uu___8 =
                   FStar_Util.format1
                     "Error extracting type definition %s to KreMLin\n" name1 in
                 (FStar_Errors.Warning_DefinitionNotTranslated, uu___8) in
               FStar_Errors.log_issue FStar_Range.dummyRange uu___7);
              FStar_Pervasives_Native.None))
and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name1 ->
          let uu___ = find_t env1 name1 in TBound uu___
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
          let uu___1 =
            let uu___2 = translate_type env1 t1 in
            let uu___3 = translate_type env1 t2 in (uu___2, uu___3) in
          TArrow uu___1
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t"))
          when is_machine_int m ->
          let uu___ = FStar_Util.must (mk_width m) in TInt uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t'"))
          when is_machine_int m ->
          let uu___ = FStar_Util.must (mk_width m) in TInt uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu___::arg::uu___1::[], p)
          when
          (((let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___2 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___2 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___2 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___2 = "FStar.HyperStack.ST.s_mref")
          -> let uu___2 = translate_type env1 arg in TBuf uu___2
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu___::[], p) when
          ((((((((((let uu___1 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu___1 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu___1 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu___1 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu___1 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu___1 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu___1 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu___1 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu___1 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___1 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___1 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu___1 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___1 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___1 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___1 = "FStar.HyperStack.ST.mmmref")
          -> let uu___1 = translate_type env1 arg in TBuf uu___1
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu___::uu___1::[], p)
          when
          let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu___2 = translate_type env1 arg in TBuf uu___2
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "LowStar.ConstBuffer.const_buffer" ->
          let uu___ = translate_type env1 arg in TConstBuf uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          (((((((((((((((let uu___ =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p in
                         uu___ = "FStar.Buffer.buffer") ||
                          (let uu___ =
                             FStar_Extraction_ML_Syntax.string_of_mlpath p in
                           uu___ = "LowStar.Buffer.buffer"))
                         ||
                         (let uu___ =
                            FStar_Extraction_ML_Syntax.string_of_mlpath p in
                          uu___ = "LowStar.ImmutableBuffer.ibuffer"))
                        ||
                        (let uu___ =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p in
                         uu___ = "LowStar.UninitializedBuffer.ubuffer"))
                       ||
                       (let uu___ =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p in
                        uu___ = "FStar.HyperStack.reference"))
                      ||
                      (let uu___ =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p in
                       uu___ = "FStar.HyperStack.stackref"))
                     ||
                     (let uu___ =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu___ = "FStar.HyperStack.ref"))
                    ||
                    (let uu___ =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu___ = "FStar.HyperStack.mmstackref"))
                   ||
                   (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu___ = "FStar.HyperStack.mmref"))
                  ||
                  (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu___ = "FStar.HyperStack.ST.reference"))
                 ||
                 (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___ = "FStar.HyperStack.ST.stackref"))
                ||
                (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___ = "FStar.HyperStack.ST.ref"))
               ||
               (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu___ = "FStar.HyperStack.ST.mmstackref"))
              ||
              (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___ = "FStar.HyperStack.ST.mmref"))
             ||
             (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___ = "Steel.Reference.ref"))
            ||
            (let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___ = "Steel.Array.array")
          -> let uu___ = translate_type env1 arg in TBuf uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu___::arg::[], p) when
          (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___1 = "FStar.HyperStack.s_ref") ||
            (let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___1 = "FStar.HyperStack.ST.s_ref")
          -> let uu___1 = translate_type env1 arg in TBuf uu___1
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu___::[], p) when
          let uu___1 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___1 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu___ = FStar_List.map (translate_type env1) args in
          TTuple uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu___ =
              let uu___1 = FStar_List.map (translate_type env1) args in
              (lid, uu___1) in
            TApp uu___
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu___ = FStar_List.map (translate_type env1) ts in TTuple uu___
and (translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
      Prims.list -> binder Prims.list)
  = fun env1 -> fun args -> FStar_List.map (translate_binder env1) args
and (translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) ->
      binder)
  =
  fun env1 ->
    fun uu___ ->
      match uu___ with
      | (name1, typ1) ->
          let uu___1 = translate_type env1 typ1 in
          { name = name1; typ = uu___1; mut = false }
and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env1 ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name1 ->
          let uu___ = find env1 name1 in EBound uu___
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op1) when
          (is_machine_int m) && (is_op op1) ->
          let uu___ =
            let uu___1 = FStar_Util.must (mk_op op1) in
            let uu___2 = FStar_Util.must (mk_width m) in (uu___1, uu___2) in
          EOp uu___
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op1) when
          is_bool_op op1 ->
          let uu___ =
            let uu___1 = FStar_Util.must (mk_bool_op op1) in (uu___1, Bool) in
          EOp uu___
      | FStar_Extraction_ML_Syntax.MLE_Name n -> EQualified n
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,
            { FStar_Extraction_ML_Syntax.mllb_name = name1;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some ([], typ1);
              FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
              FStar_Extraction_ML_Syntax.mllb_def = body;
              FStar_Extraction_ML_Syntax.mllb_meta = flags;
              FStar_Extraction_ML_Syntax.print_typ = print;_}::[]),
           continuation)
          ->
          let binder1 =
            let uu___ = translate_type env1 typ1 in
            { name = name1; typ = uu___; mut = false } in
          let body1 = translate_expr env1 body in
          let env2 = extend env1 name1 in
          let continuation1 = translate_expr env2 continuation in
          ELet (binder1, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr1, branches1) ->
          let uu___ =
            let uu___1 = translate_expr env1 expr1 in
            let uu___2 = translate_branches env1 branches1 in
            (uu___1, uu___2) in
          EMatch uu___
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_},
           arg::[])
          when
          let uu___4 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___4 = "FStar.Dyn.undyn" ->
          let uu___4 =
            let uu___5 = translate_expr env1 arg in
            let uu___6 = translate_type env1 t in (uu___5, uu___6) in
          ECast uu___4
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5)
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s);
             FStar_Extraction_ML_Syntax.mlty = uu___4;
             FStar_Extraction_ML_Syntax.loc = uu___5;_}::[])
          when
          let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "LowStar.Failure.failwith" ->
          let uu___6 = let uu___7 = translate_type env1 t in (s, uu___7) in
          EAbortT uu___6
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           arg::[])
          when
          ((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.HyperStack.All.failwith") ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "FStar.Error.unexpected"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu___5;
               FStar_Extraction_ML_Syntax.loc = uu___6;_} -> EAbortS msg
           | uu___5 ->
               let print_nm = (["FStar"; "HyperStack"; "IO"], "print_string") in
               let print =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_Name print_nm) in
               let print1 =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_App (print, [arg])) in
               let t = translate_expr env1 print1 in ESequence [t; EAbort])
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          (((((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "FStar.Buffer.index") ||
                (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___5 = "FStar.Buffer.op_Array_Access"))
               ||
               (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu___5 = "LowStar.Monotonic.Buffer.index"))
              ||
              (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "LowStar.UninitializedBuffer.uindex"))
             ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.ConstBuffer.index"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.Array.index")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufRead uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.op_Bang") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.Reference.read")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            (uu___6, (EConstant (UInt32, "0"))) in
          EBufRead uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          ((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.create") ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (Stack, uu___6, uu___7) in
          EBufCreate uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           elen::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu___5 =
            let uu___6 = translate_expr env1 elen in (Stack, uu___6) in
          EBufCreateNoInit uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           init::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.HyperStack.ST.salloc" ->
          let uu___5 =
            let uu___6 = translate_expr env1 init in
            (Stack, uu___6, (EConstant (UInt32, "1"))) in
          EBufCreate uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e2::[])
          when
          ((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.createL") ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu___5 =
            let uu___6 =
              let uu___7 = list_elements e2 in
              FStar_List.map (translate_expr env1) uu___7 in
            (Stack, uu___6) in
          EBufCreateL uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _erid::e2::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu___5 =
            let uu___6 =
              let uu___7 = list_elements e2 in
              FStar_List.map (translate_expr env1) uu___7 in
            (Eternal, uu___6) in
          EBufCreateL uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _rid::init::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.ralloc") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.HyperStack.ST.ralloc_drgn")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 init in
            (Eternal, uu___6, (EConstant (UInt32, "1"))) in
          EBufCreate uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _e0::e1::e2::[])
          when
          ((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.rcreate") ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (Eternal, uu___6, uu___7) in
          EBufCreate uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5)
          when
          (((((let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___6 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___6 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu___6 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___6 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___6 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _erid::elen::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu___5 =
            let uu___6 = translate_expr env1 elen in (Eternal, uu___6) in
          EBufCreateNoInit uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _rid::init::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.ralloc_mm") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.HyperStack.ST.ralloc_drgn_mm")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 init in
            (ManuallyManaged, uu___6, (EConstant (UInt32, "1"))) in
          EBufCreate uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           init::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.Reference.malloc" ->
          let uu___5 =
            let uu___6 = translate_expr env1 init in
            (ManuallyManaged, uu___6, (EConstant (UInt32, "1"))) in
          EBufCreate uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _e0::e1::e2::[])
          when
          (((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.Buffer.rcreate_mm") ||
              (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            (ManuallyManaged, uu___6, uu___7) in
          EBufCreate uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e0::e1::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "Steel.Array.malloc" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e0 in
            let uu___7 = translate_expr env1 e1 in
            (ManuallyManaged, uu___6, uu___7) in
          EBufCreate uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _erid::elen::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu___5 =
            let uu___6 = translate_expr env1 elen in
            (ManuallyManaged, uu___6) in
          EBufCreateNoInit uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e2::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.rfree") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.Reference.free")
          -> let uu___5 = translate_expr env1 e2 in EBufFree uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e2::[])
          when
          ((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.rfree") ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.free"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.Array.free")
          -> let uu___5 = translate_expr env1 e2 in EBufFree uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::_e3::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.Buffer.sub" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufSub uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::_e3::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ConstBuffer.sub")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufSub uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.Buffer.join" -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.Buffer.offset" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufSub uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufSub uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::e3::[])
          when
          ((((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "FStar.Buffer.upd") ||
               (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu___5 = "FStar.Buffer.op_Array_Assignment"))
              ||
              (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "LowStar.Monotonic.Buffer.upd'"))
             ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.UninitializedBuffer.uupd"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.Array.upd")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            let uu___8 = translate_expr env1 e3 in (uu___6, uu___7, uu___8) in
          EBufWrite uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.op_Colon_Equals") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "Steel.Reference.write")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            (uu___6, (EConstant (UInt32, "0")), uu___7) in
          EBufWrite uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2::[])
          when
          let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___3 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2::[])
          when
          let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___3 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::e3::e4::e5::[])
          when
          ((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.blit") ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            let uu___8 = translate_expr env1 e3 in
            let uu___9 = translate_expr env1 e4 in
            let uu___10 = translate_expr env1 e5 in
            (uu___6, uu___7, uu___8, uu___9, uu___10) in
          EBufBlit uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            let uu___8 = translate_expr env1 e3 in (uu___6, uu___7, uu___8) in
          EBufFill uu___5
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2::[])
          when
          let uu___3 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___3 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _rid::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.free_drgn") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.HyperStack.ST.new_drgn")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           _ebuf::_eseq::[])
          when
          (((let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu___5 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_},
           _eqal::e1::[])
          when
          let uu___4 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___4 = "LowStar.ConstBuffer.of_qbuf" ->
          let uu___4 =
            let uu___5 = translate_expr env1 e1 in
            let uu___6 =
              let uu___7 = translate_type env1 t in TConstBuf uu___7 in
            (uu___5, uu___6) in
          ECast uu___4
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_},
           e1::[])
          when
          ((let uu___4 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu___4 = "LowStar.ConstBuffer.cast") ||
             (let uu___4 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu___4 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu___4 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu___4 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu___4 =
            let uu___5 = translate_expr env1 e1 in
            let uu___6 = let uu___7 = translate_type env1 t in TBuf uu___7 in
            (uu___5, uu___6) in
          ECast uu___4
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           e1::[])
          when
          let uu___2 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "Obj.repr" ->
          let uu___2 = let uu___3 = translate_expr env1 e1 in (uu___3, TAny) in
          ECast uu___2
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op1);
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           args)
          when (is_machine_int m) && (is_op op1) ->
          let uu___2 = FStar_Util.must (mk_width m) in
          let uu___3 = FStar_Util.must (mk_op op1) in
          mk_op_app env1 uu___2 uu___3 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op1);
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           args)
          when is_bool_op op1 ->
          let uu___2 = FStar_Util.must (mk_bool_op op1) in
          mk_op_app env1 Bool uu___2 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_}::[])
          when is_machine_int m ->
          let uu___4 =
            let uu___5 = FStar_Util.must (mk_width m) in (uu___5, c) in
          EConstant uu___4
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_}::[])
          when is_machine_int m ->
          let uu___4 =
            let uu___5 = FStar_Util.must (mk_width m) in (uu___5, c) in
          EConstant uu___4
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[], "string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu___4 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu___4 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu___4 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu___;
                  FStar_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStar_Extraction_ML_Syntax.mlty = uu___3;
             FStar_Extraction_ML_Syntax.loc = uu___4;_},
           { FStar_Extraction_ML_Syntax.expr = ebefore;
             FStar_Extraction_ML_Syntax.mlty = uu___5;
             FStar_Extraction_ML_Syntax.loc = uu___6;_}::e1::{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = eafter;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 = uu___7;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 = uu___8;_}::[])
          when
          let uu___9 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___9 = "LowStar.Comment.comment_gen" ->
          (match (ebefore, eafter) with
           | (FStar_Extraction_ML_Syntax.MLE_Const
              (FStar_Extraction_ML_Syntax.MLC_String sbefore),
              FStar_Extraction_ML_Syntax.MLE_Const
              (FStar_Extraction_ML_Syntax.MLC_String safter)) ->
               (if FStar_Util.contains sbefore "*/"
                then failwith "Before Comment contains end-of-comment marker"
                else ();
                if FStar_Util.contains safter "*/"
                then failwith "After Comment contains end-of-comment marker"
                else ();
                (let uu___11 =
                   let uu___12 = translate_expr env1 e1 in
                   (sbefore, uu___12, safter) in
                 EComment uu___11))
           | uu___9 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_}::[])
          when
          let uu___4 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu___4 = "LowStar.Comment.comment" ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               (if FStar_Util.contains s "*/"
                then
                  failwith
                    "Standalone Comment contains end-of-comment marker"
                else ();
                EStandaloneComment s)
           | uu___4 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[], "buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu___2;
             FStar_Extraction_ML_Syntax.loc = uu___3;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu___4 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[], c);
             FStar_Extraction_ML_Syntax.mlty = uu___;
             FStar_Extraction_ML_Syntax.loc = uu___1;_},
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
            let uu___2 =
              let uu___3 = translate_expr env1 arg in (uu___3, (TInt UInt64)) in
            ECast uu___2
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu___3 =
                 let uu___4 = translate_expr env1 arg in
                 (uu___4, (TInt UInt32)) in
               ECast uu___3)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu___4 =
                   let uu___5 = translate_expr env1 arg in
                   (uu___5, (TInt UInt16)) in
                 ECast uu___4)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu___5 =
                     let uu___6 = translate_expr env1 arg in
                     (uu___6, (TInt UInt8)) in
                   ECast uu___5)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu___6 =
                       let uu___7 = translate_expr env1 arg in
                       (uu___7, (TInt Int64)) in
                     ECast uu___6)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu___7 =
                         let uu___8 = translate_expr env1 arg in
                         (uu___8, (TInt Int32)) in
                       ECast uu___7)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu___8 =
                           let uu___9 = translate_expr env1 arg in
                           (uu___9, (TInt Int16)) in
                         ECast uu___8)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu___9 =
                             let uu___10 = translate_expr env1 arg in
                             (uu___10, (TInt Int8)) in
                           ECast uu___9)
                        else
                          (let uu___10 =
                             let uu___11 =
                               let uu___12 = translate_expr env1 arg in
                               [uu___12] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu___11) in
                           EApp uu___10)
      | FStar_Extraction_ML_Syntax.MLE_App (head, args) ->
          let uu___ =
            let uu___1 = translate_expr env1 head in
            let uu___2 = FStar_List.map (translate_expr env1) args in
            (uu___1, uu___2) in
          EApp uu___
      | FStar_Extraction_ML_Syntax.MLE_TApp (head, ty_args) ->
          let uu___ =
            let uu___1 = translate_expr env1 head in
            let uu___2 = FStar_List.map (translate_type env1) ty_args in
            (uu___1, uu___2) in
          ETypApp uu___
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) ->
          let uu___ =
            let uu___1 = translate_expr env1 e1 in
            let uu___2 = translate_type env1 t_to in (uu___1, uu___2) in
          ECast uu___
      | FStar_Extraction_ML_Syntax.MLE_Record (uu___, fields) ->
          let uu___1 =
            let uu___2 = assert_lid env1 e.FStar_Extraction_ML_Syntax.mlty in
            let uu___3 =
              FStar_List.map
                (fun uu___4 ->
                   match uu___4 with
                   | (field, expr1) ->
                       let uu___5 = translate_expr env1 expr1 in
                       (field, uu___5)) fields in
            (uu___2, uu___3) in
          EFlat uu___1
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) ->
          let uu___ =
            let uu___1 = assert_lid env1 e1.FStar_Extraction_ML_Syntax.mlty in
            let uu___2 = translate_expr env1 e1 in
            (uu___1, uu___2, (FStar_Pervasives_Native.snd path)) in
          EField uu___
      | FStar_Extraction_ML_Syntax.MLE_Let uu___ ->
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_Code.string_of_mlexpr ([], "") e in
            FStar_Util.format1 "todo: translate_expr [MLE_Let] (expr is: %s)"
              uu___2 in
          failwith uu___1
      | FStar_Extraction_ML_Syntax.MLE_App (head, uu___) ->
          let uu___1 =
            let uu___2 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu___2 in
          failwith uu___1
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu___ = FStar_List.map (translate_expr env1) seqs in
          ESequence uu___
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu___ = FStar_List.map (translate_expr env1) es in ETuple uu___
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu___, cons), es) ->
          let uu___1 =
            let uu___2 = assert_lid env1 e.FStar_Extraction_ML_Syntax.mlty in
            let uu___3 = FStar_List.map (translate_expr env1) es in
            (uu___2, cons, uu___3) in
          ECons uu___1
      | FStar_Extraction_ML_Syntax.MLE_Fun (args, body) ->
          let binders = translate_binders env1 args in
          let env2 = add_binders env1 args in
          let uu___ =
            let uu___1 = translate_expr env2 body in
            let uu___2 =
              translate_type env2 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu___1, uu___2) in
          EFun uu___
      | FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) ->
          let uu___ =
            let uu___1 = translate_expr env1 e1 in
            let uu___2 = translate_expr env1 e2 in
            let uu___3 =
              match e3 with
              | FStar_Pervasives_Native.None -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env1 e31 in
            (uu___1, uu___2, uu___3) in
          EIfThenElse uu___
      | FStar_Extraction_ML_Syntax.MLE_Raise uu___ ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu___ ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu___ ->
          failwith "todo: translate_expr [MLE_Coerce]"
and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu___ =
              let uu___1 = FStar_List.map (translate_type env1) ts in
              (lid, uu___1) in
            TApp uu___
          else TQualified lid
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu___2 in
          failwith uu___1
and (translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)
      Prims.list -> (pattern * expr) Prims.list)
  =
  fun env1 ->
    fun branches1 -> FStar_List.map (translate_branch env1) branches1
and (translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) ->
      (pattern * expr))
  =
  fun env1 ->
    fun uu___ ->
      match uu___ with
      | (pat, guard, expr1) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu___1 = translate_pat env1 pat in
            (match uu___1 with
             | (env2, pat1) ->
                 let uu___2 = translate_expr env2 expr1 in (pat1, uu___2))
          else failwith "todo: translate_branch"
and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___ ->
    match uu___ with
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
  fun env1 ->
    fun p ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit) -> (env1, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env1, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Int (s, sw)) ->
          let uu___ =
            let uu___1 = let uu___2 = translate_width sw in (uu___2, s) in
            PConstant uu___1 in
          (env1, uu___)
      | FStar_Extraction_ML_Syntax.MLP_Var name1 ->
          let env2 = extend env1 name1 in
          (env2, (PVar { name = name1; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild ->
          let env2 = extend env1 "_" in
          (env2, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu___, cons), ps) ->
          let uu___1 =
            FStar_List.fold_left
              (fun uu___2 ->
                 fun p1 ->
                   match uu___2 with
                   | (env2, acc) ->
                       let uu___3 = translate_pat env2 p1 in
                       (match uu___3 with | (env3, p2) -> (env3, (p2 :: acc))))
              (env1, []) ps in
          (match uu___1 with
           | (env2, ps1) -> (env2, (PCons (cons, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu___, ps) ->
          let uu___1 =
            FStar_List.fold_left
              (fun uu___2 ->
                 fun uu___3 ->
                   match (uu___2, uu___3) with
                   | ((env2, acc), (field, p1)) ->
                       let uu___4 = translate_pat env2 p1 in
                       (match uu___4 with
                        | (env3, p2) -> (env3, ((field, p2) :: acc))))
              (env1, []) ps in
          (match uu___1 with
           | (env2, ps1) -> (env2, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu___ =
            FStar_List.fold_left
              (fun uu___1 ->
                 fun p1 ->
                   match uu___1 with
                   | (env2, acc) ->
                       let uu___2 = translate_pat env2 p1 in
                       (match uu___2 with | (env3, p2) -> (env3, (p2 :: acc))))
              (env1, []) ps in
          (match uu___ with
           | (env2, ps1) -> (env2, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu___ ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu___ ->
          failwith "todo: translate_pat [MLP_Branch]"
and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu___1 =
            let uu___2 = FStar_String.list_of_string s in
            FStar_All.pipe_right uu___2
              (FStar_Util.for_some
                 (fun c1 -> c1 = (FStar_Char.char_of_int Prims.int_zero))) in
          if uu___1
          then
            let uu___2 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu___2
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1 in
        let s = FStar_Util.string_of_int i in
        let c2 = EConstant (UInt32, s) in
        let char_of_int = EQualified (["FStar"; "Char"], "char_of_int") in
        EApp (char_of_int, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some (sg, wd)) ->
        let uu___ =
          let uu___1 =
            translate_width (FStar_Pervasives_Native.Some (sg, wd)) in
          (uu___1, s) in
        EConstant uu___
    | FStar_Extraction_ML_Syntax.MLC_Float uu___ ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu___ ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) ->
        EConstant (CInt, s)
and (mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr)
  =
  fun env1 ->
    fun w ->
      fun op1 ->
        fun args ->
          let uu___ =
            let uu___1 = FStar_List.map (translate_expr env1) args in
            ((EOp (op1, w)), uu___1) in
          EApp uu___
let (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu___ ->
    match uu___ with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m ->
             let m_name =
               let uu___1 = m in
               match uu___1 with
               | (path, uu___2, uu___3) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path in
             try
               (fun uu___1 ->
                  match () with
                  | () ->
                      ((let uu___3 =
                          let uu___4 = FStar_Options.silent () in
                          Prims.op_Negation uu___4 in
                        if uu___3
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu___3 = translate_module m in
                        FStar_Pervasives_Native.Some uu___3))) ()
             with
             | uu___1 ->
                 ((let uu___3 = FStar_Util.print_exn uu___1 in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu___3);
                  FStar_Pervasives_Native.None)) modules