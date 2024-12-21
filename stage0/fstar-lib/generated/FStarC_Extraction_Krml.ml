open Prims
type version = Prims.int
let (current_version : version) = (Prims.of_int (31))
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
  | CNoInline 
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
  | EAddrOf of expr 
  | EBufNull of typ 
  | EBufDiff of (expr * expr) 
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
  | SizeT 
  | PtrdiffT 
and binder =
  {
  name: Prims.string ;
  typ: typ ;
  mut: Prims.bool ;
  meta: flag Prims.list }
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
  | TArray of (typ * (width * Prims.string)) 
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
let (uu___is_DUntaggedUnion : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DUntaggedUnion _0 -> true | uu___ -> false
let (__proj__DUntaggedUnion__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * typ) Prims.list))
  = fun projectee -> match projectee with | DUntaggedUnion _0 -> _0
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
let (uu___is_CNoInline : flag -> Prims.bool) =
  fun projectee -> match projectee with | CNoInline -> true | uu___ -> false
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
let (uu___is_EAddrOf : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAddrOf _0 -> true | uu___ -> false
let (__proj__EAddrOf__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EAddrOf _0 -> _0
let (uu___is_EBufNull : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufNull _0 -> true | uu___ -> false
let (__proj__EBufNull__item___0 : expr -> typ) =
  fun projectee -> match projectee with | EBufNull _0 -> _0
let (uu___is_EBufDiff : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufDiff _0 -> true | uu___ -> false
let (__proj__EBufDiff__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufDiff _0 -> _0
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
let (uu___is_SizeT : width -> Prims.bool) =
  fun projectee -> match projectee with | SizeT -> true | uu___ -> false
let (uu___is_PtrdiffT : width -> Prims.bool) =
  fun projectee -> match projectee with | PtrdiffT -> true | uu___ -> false
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee ->
    match projectee with | { name; typ = typ1; mut; meta;_} -> name
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee ->
    match projectee with | { name; typ = typ1; mut; meta;_} -> typ1
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee ->
    match projectee with | { name; typ = typ1; mut; meta;_} -> mut
let (__proj__Mkbinder__item__meta : binder -> flag Prims.list) =
  fun projectee ->
    match projectee with | { name; typ = typ1; mut; meta;_} -> meta
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
let (uu___is_TArray : typ -> Prims.bool) =
  fun projectee -> match projectee with | TArray _0 -> true | uu___ -> false
let (__proj__TArray__item___0 : typ -> (typ * (width * Prims.string))) =
  fun projectee -> match projectee with | TArray _0 -> _0
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
let (pretty_width : width FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | UInt8 -> FStarC_Pprint.doc_of_string "UInt8"
         | UInt16 -> FStarC_Pprint.doc_of_string "UInt16"
         | UInt32 -> FStarC_Pprint.doc_of_string "UInt32"
         | UInt64 -> FStarC_Pprint.doc_of_string "UInt64"
         | Int8 -> FStarC_Pprint.doc_of_string "Int8"
         | Int16 -> FStarC_Pprint.doc_of_string "Int16"
         | Int32 -> FStarC_Pprint.doc_of_string "Int32"
         | Int64 -> FStarC_Pprint.doc_of_string "Int64"
         | Bool -> FStarC_Pprint.doc_of_string "Bool"
         | CInt -> FStarC_Pprint.doc_of_string "CInt"
         | SizeT -> FStarC_Pprint.doc_of_string "SizeT"
         | PtrdiffT -> FStarC_Pprint.doc_of_string "PtrdiffT")
  }
let (record_string :
  (Prims.string * Prims.string) Prims.list -> Prims.string) =
  fun fs ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Compiler_List.map
            (fun uu___3 ->
               match uu___3 with
               | (f, s) -> Prims.strcat f (Prims.strcat " = " s)) fs in
        FStarC_Compiler_String.concat "; " uu___2 in
      Prims.strcat uu___1 "}" in
    Prims.strcat "{" uu___
let (ctor :
  Prims.string -> FStarC_Pprint.document Prims.list -> FStarC_Pprint.document)
  =
  fun n ->
    fun args ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Pprint.break_ Prims.int_one in
            let uu___4 =
              let uu___5 = FStarC_Pprint.doc_of_string n in uu___5 :: args in
            FStarC_Pprint.flow uu___3 uu___4 in
          FStarC_Pprint.parens uu___2 in
        FStarC_Pprint.group uu___1 in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___
let pp_list' :
  'a .
    ('a -> FStarC_Pprint.document) -> 'a Prims.list -> FStarC_Pprint.document
  =
  fun f ->
    fun xs ->
      (FStarC_Class_PP.pp_list { FStarC_Class_PP.pp = f }).FStarC_Class_PP.pp
        xs
let rec (typ_to_doc : typ -> FStarC_Pprint.document) =
  fun t ->
    match t with
    | TInt w ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_width w in [uu___1] in
        ctor "TInt" uu___
    | TBuf t1 ->
        let uu___ = let uu___1 = typ_to_doc t1 in [uu___1] in
        ctor "TBuf" uu___
    | TUnit -> FStarC_Pprint.doc_of_string "TUnit"
    | TQualified x ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Class_Show.show
                (FStarC_Class_Show.show_tuple2
                   (FStarC_Class_Show.show_list
                      FStarC_Class_Show.showable_string)
                   FStarC_Class_Show.showable_string) x in
            FStarC_Pprint.doc_of_string uu___2 in
          [uu___1] in
        ctor "TQualified" uu___
    | TBool -> FStarC_Pprint.doc_of_string "TBool"
    | TAny -> FStarC_Pprint.doc_of_string "TAny"
    | TArrow (t1, t2) ->
        let uu___ =
          let uu___1 = typ_to_doc t1 in
          let uu___2 = let uu___3 = typ_to_doc t2 in [uu___3] in uu___1 ::
            uu___2 in
        ctor "TArrow" uu___
    | TBound x ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int x in
          [uu___1] in
        ctor "TBound" uu___
    | TApp (x, xs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Class_Show.show
                (FStarC_Class_Show.show_tuple2
                   (FStarC_Class_Show.show_list
                      FStarC_Class_Show.showable_string)
                   FStarC_Class_Show.showable_string) x in
            FStarC_Pprint.doc_of_string uu___2 in
          let uu___2 = let uu___3 = pp_list' typ_to_doc xs in [uu___3] in
          uu___1 :: uu___2 in
        ctor "TApp" uu___
    | TTuple ts ->
        let uu___ = let uu___1 = pp_list' typ_to_doc ts in [uu___1] in
        ctor "TTuple" uu___
    | TConstBuf t1 ->
        let uu___ = let uu___1 = typ_to_doc t1 in [uu___1] in
        ctor "TConstBuf" uu___
    | TArray (t1, c) ->
        let uu___ =
          let uu___1 = typ_to_doc t1 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStarC_Class_PP.pp pretty_width
                      (FStar_Pervasives_Native.fst c) in
                  let uu___7 =
                    let uu___8 =
                      FStarC_Pprint.doc_of_string
                        (FStar_Pervasives_Native.snd c) in
                    [uu___8] in
                  uu___6 :: uu___7 in
                FStarC_Pprint.separate FStarC_Pprint.comma uu___5 in
              FStarC_Pprint.parens uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        ctor "TArray" uu___
let (pretty_typ : typ FStarC_Class_PP.pretty) =
  { FStarC_Class_PP.pp = typ_to_doc }
let (pretty_string : Prims.string FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun s ->
         let uu___ = FStarC_Pprint.doc_of_string s in
         FStarC_Pprint.dquotes uu___)
  }
let (pretty_flag : flag FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | Private -> FStarC_Pprint.doc_of_string "Private"
         | WipeBody -> FStarC_Pprint.doc_of_string "WipeBody"
         | CInline -> FStarC_Pprint.doc_of_string "CInline"
         | Substitute -> FStarC_Pprint.doc_of_string "Substitute"
         | GCType -> FStarC_Pprint.doc_of_string "GCType"
         | Comment s ->
             let uu___1 =
               let uu___2 = FStarC_Class_PP.pp pretty_string s in [uu___2] in
             ctor "Comment" uu___1
         | MustDisappear -> FStarC_Pprint.doc_of_string "MustDisappear"
         | Const s ->
             let uu___1 =
               let uu___2 = FStarC_Class_PP.pp pretty_string s in [uu___2] in
             ctor "Const" uu___1
         | Prologue s ->
             let uu___1 =
               let uu___2 = FStarC_Class_PP.pp pretty_string s in [uu___2] in
             ctor "Prologue" uu___1
         | Epilogue s ->
             let uu___1 =
               let uu___2 = FStarC_Class_PP.pp pretty_string s in [uu___2] in
             ctor "Epilogue" uu___1
         | Abstract -> FStarC_Pprint.doc_of_string "Abstract"
         | IfDef -> FStarC_Pprint.doc_of_string "IfDef"
         | Macro -> FStarC_Pprint.doc_of_string "Macro"
         | Deprecated s ->
             let uu___1 =
               let uu___2 = FStarC_Class_PP.pp pretty_string s in [uu___2] in
             ctor "Deprecated" uu___1
         | CNoInline -> FStarC_Pprint.doc_of_string "CNoInline")
  }
let (spaced : FStarC_Pprint.document -> FStarC_Pprint.document) =
  fun a ->
    let uu___ = FStarC_Pprint.break_ Prims.int_one in
    let uu___1 =
      let uu___2 = FStarC_Pprint.break_ Prims.int_one in
      FStarC_Pprint.op_Hat_Hat a uu___2 in
    FStarC_Pprint.op_Hat_Hat uu___ uu___1
let (record : FStarC_Pprint.document Prims.list -> FStarC_Pprint.document) =
  fun fs ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Pprint.break_ Prims.int_one in
              FStarC_Pprint.op_Hat_Hat FStarC_Pprint.semi uu___5 in
            FStarC_Pprint.separate uu___4 fs in
          spaced uu___3 in
        FStarC_Pprint.braces uu___2 in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___1 in
    FStarC_Pprint.group uu___
let (fld : Prims.string -> FStarC_Pprint.document -> FStarC_Pprint.document)
  =
  fun n ->
    fun v ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Pprint.doc_of_string (Prims.strcat n " =") in
          FStarC_Pprint.op_Hat_Slash_Hat uu___2 v in
        FStarC_Pprint.nest (Prims.of_int (2)) uu___1 in
      FStarC_Pprint.group uu___
let (pretty_binder : binder FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun b ->
         let uu___ =
           let uu___1 =
             let uu___2 = FStarC_Class_PP.pp pretty_string b.name in
             fld "name" uu___2 in
           let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_Class_PP.pp pretty_typ b.typ in
               fld "typ" uu___4 in
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   FStarC_Class_PP.pp FStarC_Class_PP.pp_bool b.mut in
                 fld "mut" uu___6 in
               let uu___6 =
                 let uu___7 =
                   let uu___8 =
                     FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag)
                       b.meta in
                   fld "meta" uu___8 in
                 [uu___7] in
               uu___5 :: uu___6 in
             uu___3 :: uu___4 in
           uu___1 :: uu___2 in
         record uu___)
  }
let (pretty_lifetime : lifetime FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | Eternal -> FStarC_Pprint.doc_of_string "Eternal"
         | Stack -> FStarC_Pprint.doc_of_string "Stack"
         | ManuallyManaged -> FStarC_Pprint.doc_of_string "ManuallyManaged")
  }
let (pretty_op : op FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | Add -> FStarC_Pprint.doc_of_string "Add"
         | AddW -> FStarC_Pprint.doc_of_string "AddW"
         | Sub -> FStarC_Pprint.doc_of_string "Sub"
         | SubW -> FStarC_Pprint.doc_of_string "SubW"
         | Div -> FStarC_Pprint.doc_of_string "Div"
         | DivW -> FStarC_Pprint.doc_of_string "DivW"
         | Mult -> FStarC_Pprint.doc_of_string "Mult"
         | MultW -> FStarC_Pprint.doc_of_string "MultW"
         | Mod -> FStarC_Pprint.doc_of_string "Mod"
         | BOr -> FStarC_Pprint.doc_of_string "BOr"
         | BAnd -> FStarC_Pprint.doc_of_string "BAnd"
         | BXor -> FStarC_Pprint.doc_of_string "BXor"
         | BShiftL -> FStarC_Pprint.doc_of_string "BShiftL"
         | BShiftR -> FStarC_Pprint.doc_of_string "BShiftR"
         | BNot -> FStarC_Pprint.doc_of_string "BNot"
         | Eq -> FStarC_Pprint.doc_of_string "Eq"
         | Neq -> FStarC_Pprint.doc_of_string "Neq"
         | Lt -> FStarC_Pprint.doc_of_string "Lt"
         | Lte -> FStarC_Pprint.doc_of_string "Lte"
         | Gt -> FStarC_Pprint.doc_of_string "Gt"
         | Gte -> FStarC_Pprint.doc_of_string "Gte"
         | And -> FStarC_Pprint.doc_of_string "And"
         | Or -> FStarC_Pprint.doc_of_string "Or"
         | Xor -> FStarC_Pprint.doc_of_string "Xor"
         | Not -> FStarC_Pprint.doc_of_string "Not")
  }
let (pretty_cc : cc FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | StdCall -> FStarC_Pprint.doc_of_string "StdCall"
         | CDecl -> FStarC_Pprint.doc_of_string "CDecl"
         | FastCall -> FStarC_Pprint.doc_of_string "FastCall")
  }
let rec (pattern_to_doc : pattern -> FStarC_Pprint.document) =
  fun p ->
    match p with
    | PUnit -> FStarC_Pprint.doc_of_string "PUnit"
    | PBool b ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool b in
          [uu___1] in
        ctor "PBool" uu___
    | PVar b ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_binder b in [uu___1] in
        ctor "PVar" uu___
    | PCons (x, ps) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_string x in
          let uu___2 = let uu___3 = pp_list' pattern_to_doc ps in [uu___3] in
          uu___1 :: uu___2 in
        ctor "PCons" uu___
    | PTuple ps ->
        let uu___ = let uu___1 = pp_list' pattern_to_doc ps in [uu___1] in
        ctor "PTuple" uu___
    | PRecord fs ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (s, p1) ->
                       let uu___4 = pattern_to_doc p1 in fld s uu___4) fs in
            record uu___2 in
          [uu___1] in
        ctor "PRecord" uu___
    | PConstant c ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp
              (FStarC_Class_PP.pp_tuple2 pretty_width pretty_string) c in
          [uu___1] in
        ctor "PConstant" uu___
let (pretty_pattern : pattern FStarC_Class_PP.pretty) =
  { FStarC_Class_PP.pp = pattern_to_doc }
let rec (decl_to_doc : decl -> FStarC_Pprint.document) =
  fun d ->
    match d with
    | DGlobal (fs, x, i, t, e) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag) fs in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp
                (FStarC_Class_PP.pp_tuple2
                   (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int i in
              let uu___6 =
                let uu___7 = FStarC_Class_PP.pp pretty_typ t in
                let uu___8 = let uu___9 = expr_to_doc e in [uu___9] in uu___7
                  :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "DGlobal" uu___
    | DFunction (cc1, fs, i, t, x, bs, e) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_option pretty_cc) cc1 in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag) fs in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int i in
              let uu___6 =
                let uu___7 = FStarC_Class_PP.pp pretty_typ t in
                let uu___8 =
                  let uu___9 =
                    FStarC_Class_PP.pp
                      (FStarC_Class_PP.pp_tuple2
                         (FStarC_Class_PP.pp_list pretty_string)
                         pretty_string) x in
                  let uu___10 =
                    let uu___11 =
                      FStarC_Class_PP.pp
                        (FStarC_Class_PP.pp_list pretty_binder) bs in
                    let uu___12 = let uu___13 = expr_to_doc e in [uu___13] in
                    uu___11 :: uu___12 in
                  uu___9 :: uu___10 in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "DFunction" uu___
    | DTypeAlias (x, fs, i, t) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp
              (FStarC_Class_PP.pp_tuple2
                 (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag) fs in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int i in
              let uu___6 =
                let uu___7 = FStarC_Class_PP.pp pretty_typ t in [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "DTypeAlias" uu___
    | DTypeFlat (x, fs, i, f) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp
              (FStarC_Class_PP.pp_tuple2
                 (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag) fs in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int i in
              let uu___6 =
                let uu___7 =
                  FStarC_Class_PP.pp
                    (FStarC_Class_PP.pp_list
                       (FStarC_Class_PP.pp_tuple2 pretty_string
                          (FStarC_Class_PP.pp_tuple2 pretty_typ
                             FStarC_Class_PP.pp_bool))) f in
                [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "DTypeFlat" uu___
    | DUnusedRetainedForBackwardsCompat (cc1, fs, x, t) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_option pretty_cc) cc1 in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag) fs in
            let uu___4 =
              let uu___5 =
                FStarC_Class_PP.pp
                  (FStarC_Class_PP.pp_tuple2
                     (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
              let uu___6 =
                let uu___7 = FStarC_Class_PP.pp pretty_typ t in [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "DUnusedRetainedForBackwardsCompat" uu___
    | DTypeVariant (x, fs, i, bs) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp
              (FStarC_Class_PP.pp_tuple2
                 (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag) fs in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int i in
              let uu___6 =
                let uu___7 =
                  FStarC_Class_PP.pp
                    (FStarC_Class_PP.pp_list
                       (FStarC_Class_PP.pp_tuple2 pretty_string
                          (FStarC_Class_PP.pp_list
                             (FStarC_Class_PP.pp_tuple2 pretty_string
                                (FStarC_Class_PP.pp_tuple2 pretty_typ
                                   FStarC_Class_PP.pp_bool))))) bs in
                [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "DTypeVariant" uu___
    | DTypeAbstractStruct x ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp
              (FStarC_Class_PP.pp_tuple2
                 (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
          [uu___1] in
        ctor "DTypeAbstractStruct" uu___
    | DExternal (cc1, fs, x, t, xs) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_option pretty_cc) cc1 in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag) fs in
            let uu___4 =
              let uu___5 =
                FStarC_Class_PP.pp
                  (FStarC_Class_PP.pp_tuple2
                     (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
              let uu___6 =
                let uu___7 = FStarC_Class_PP.pp pretty_typ t in
                let uu___8 =
                  let uu___9 =
                    FStarC_Class_PP.pp
                      (FStarC_Class_PP.pp_list pretty_string) xs in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "DExternal" uu___
    | DUntaggedUnion (x, fs, i, xs) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp
              (FStarC_Class_PP.pp_tuple2
                 (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_flag) fs in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int i in
              let uu___6 =
                let uu___7 =
                  FStarC_Class_PP.pp
                    (FStarC_Class_PP.pp_list
                       (FStarC_Class_PP.pp_tuple2 pretty_string pretty_typ))
                    xs in
                [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "DUntaggedUnion" uu___
and (expr_to_doc : expr -> FStarC_Pprint.document) =
  fun e ->
    match e with
    | EBound x ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int x in
          [uu___1] in
        ctor "EBound" uu___
    | EQualified x ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp
              (FStarC_Class_PP.pp_tuple2
                 (FStarC_Class_PP.pp_list pretty_string) pretty_string) x in
          [uu___1] in
        ctor "EQualified" uu___
    | EConstant x ->
        let uu___ =
          let uu___1 =
            FStarC_Class_PP.pp
              (FStarC_Class_PP.pp_tuple2 pretty_width pretty_string) x in
          [uu___1] in
        ctor "EConstant" uu___
    | EUnit -> FStarC_Pprint.doc_of_string "EUnit"
    | EApp (x, xs) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 = let uu___3 = pp_list' expr_to_doc xs in [uu___3] in
          uu___1 :: uu___2 in
        ctor "EApp" uu___
    | ETypApp (x, xs) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 =
            let uu___3 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_typ) xs in
            [uu___3] in
          uu___1 :: uu___2 in
        ctor "ETypApp" uu___
    | ELet (x, y, z) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_binder x in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 = let uu___5 = expr_to_doc z in [uu___5] in uu___3 ::
              uu___4 in
          uu___1 :: uu___2 in
        ctor "ELet" uu___
    | EIfThenElse (x, y, z) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 = let uu___5 = expr_to_doc z in [uu___5] in uu___3 ::
              uu___4 in
          uu___1 :: uu___2 in
        ctor "EIfThenElse" uu___
    | ESequence xs ->
        let uu___ = let uu___1 = pp_list' expr_to_doc xs in [uu___1] in
        ctor "ESequence" uu___
    | EAssign (x, y) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 = let uu___3 = expr_to_doc y in [uu___3] in uu___1 ::
            uu___2 in
        ctor "EAssign" uu___
    | EBufCreate (x, y, z) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_lifetime x in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 = let uu___5 = expr_to_doc z in [uu___5] in uu___3 ::
              uu___4 in
          uu___1 :: uu___2 in
        ctor "EBufCreate" uu___
    | EBufRead (x, y) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 = let uu___3 = expr_to_doc y in [uu___3] in uu___1 ::
            uu___2 in
        ctor "EBufRead" uu___
    | EBufWrite (x, y, z) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 = let uu___5 = expr_to_doc z in [uu___5] in uu___3 ::
              uu___4 in
          uu___1 :: uu___2 in
        ctor "EBufWrite" uu___
    | EBufSub (x, y) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 = let uu___3 = expr_to_doc y in [uu___3] in uu___1 ::
            uu___2 in
        ctor "EBufSub" uu___
    | EBufBlit (x, y, z, a, b) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 =
              let uu___5 = expr_to_doc z in
              let uu___6 =
                let uu___7 = expr_to_doc a in
                let uu___8 = let uu___9 = expr_to_doc b in [uu___9] in uu___7
                  :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "EBufBlit" uu___
    | EMatch (x, bs) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 = let uu___3 = pp_list' pp_branch bs in [uu___3] in
          uu___1 :: uu___2 in
        ctor "EMatch" uu___
    | EOp (x, y) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_op x in
          let uu___2 =
            let uu___3 = FStarC_Class_PP.pp pretty_width y in [uu___3] in
          uu___1 :: uu___2 in
        ctor "EOp" uu___
    | ECast (x, y) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 =
            let uu___3 = FStarC_Class_PP.pp pretty_typ y in [uu___3] in
          uu___1 :: uu___2 in
        ctor "ECast" uu___
    | EPushFrame -> FStarC_Pprint.doc_of_string "EPushFrame"
    | EPopFrame -> FStarC_Pprint.doc_of_string "EPopFrame"
    | EBool x ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool x in
          [uu___1] in
        ctor "EBool" uu___
    | EAny -> FStarC_Pprint.doc_of_string "EAny"
    | EAbort -> FStarC_Pprint.doc_of_string "EAbort"
    | EReturn x ->
        let uu___ = let uu___1 = expr_to_doc x in [uu___1] in
        ctor "EReturn" uu___
    | EFlat (x, xs) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_typ x in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_Compiler_List.map
                  (fun uu___5 ->
                     match uu___5 with
                     | (s, e1) -> let uu___6 = expr_to_doc e1 in fld s uu___6)
                  xs in
              record uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        ctor "EFlat" uu___
    | EField (x, y, z) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_typ x in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp pretty_string z in [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "EField" uu___
    | EWhile (x, y) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 = let uu___3 = expr_to_doc y in [uu___3] in uu___1 ::
            uu___2 in
        ctor "EWhile" uu___
    | EBufCreateL (x, xs) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_lifetime x in
          let uu___2 = let uu___3 = pp_list' expr_to_doc xs in [uu___3] in
          uu___1 :: uu___2 in
        ctor "EBufCreateL" uu___
    | ETuple xs ->
        let uu___ = let uu___1 = pp_list' expr_to_doc xs in [uu___1] in
        ctor "ETuple" uu___
    | ECons (x, y, xs) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_typ x in
          let uu___2 =
            let uu___3 = FStarC_Class_PP.pp pretty_string y in
            let uu___4 = let uu___5 = pp_list' expr_to_doc xs in [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "ECons" uu___
    | EBufFill (x, y, z) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 = let uu___5 = expr_to_doc z in [uu___5] in uu___3 ::
              uu___4 in
          uu___1 :: uu___2 in
        ctor "EBufFill" uu___
    | EString x ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_string x in [uu___1] in
        ctor "EString" uu___
    | EFun (xs, y, z) ->
        let uu___ =
          let uu___1 = pp_list' (FStarC_Class_PP.pp pretty_binder) xs in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp pretty_typ z in [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "EFun" uu___
    | EAbortS x ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_string x in [uu___1] in
        ctor "EAbortS" uu___
    | EBufFree x ->
        let uu___ = let uu___1 = expr_to_doc x in [uu___1] in
        ctor "EBufFree" uu___
    | EBufCreateNoInit (x, y) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_lifetime x in
          let uu___2 = let uu___3 = expr_to_doc y in [uu___3] in uu___1 ::
            uu___2 in
        ctor "EBufCreateNoInit" uu___
    | EAbortT (x, y) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_string x in
          let uu___2 =
            let uu___3 = FStarC_Class_PP.pp pretty_typ y in [uu___3] in
          uu___1 :: uu___2 in
        ctor "EAbortT" uu___
    | EComment (x, y, z) ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_string x in
          let uu___2 =
            let uu___3 = expr_to_doc y in
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp pretty_string z in [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        ctor "EComment" uu___
    | EStandaloneComment x ->
        let uu___ =
          let uu___1 = FStarC_Class_PP.pp pretty_string x in [uu___1] in
        ctor "EStandaloneComment" uu___
    | EAddrOf x ->
        let uu___ = let uu___1 = expr_to_doc x in [uu___1] in
        ctor "EAddrOf" uu___
    | EBufNull x ->
        let uu___ = let uu___1 = FStarC_Class_PP.pp pretty_typ x in [uu___1] in
        ctor "EBufNull" uu___
    | EBufDiff (x, y) ->
        let uu___ =
          let uu___1 = expr_to_doc x in
          let uu___2 = let uu___3 = expr_to_doc y in [uu___3] in uu___1 ::
            uu___2 in
        ctor "EBufDiff" uu___
and (pp_branch : branch -> FStarC_Pprint.document) =
  fun b ->
    let uu___ = b in
    match uu___ with
    | (p, e) ->
        let uu___1 =
          let uu___2 = FStarC_Class_PP.pp pretty_pattern p in
          let uu___3 =
            let uu___4 = expr_to_doc e in
            FStarC_Pprint.op_Hat_Slash_Hat FStarC_Pprint.comma uu___4 in
          FStarC_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStarC_Pprint.parens uu___1
let (pretty_decl : decl FStarC_Class_PP.pretty) =
  { FStarC_Class_PP.pp = decl_to_doc }
let (showable_decl : decl FStarC_Class_Show.showable) =
  FStarC_Class_PP.showable_from_pretty pretty_decl
type program = decl Prims.list
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
    | "SizeT" -> FStar_Pervasives_Native.Some SizeT
    | "PtrdiffT" -> FStar_Pervasives_Native.Some PtrdiffT
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
    | "mul_underspec" -> FStar_Pervasives_Native.Some Mult
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
  uenv: FStarC_Extraction_ML_UEnv.uenv ;
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }
and name = {
  pretty: Prims.string }
let (__proj__Mkenv__item__uenv : env -> FStarC_Extraction_ML_UEnv.uenv) =
  fun projectee ->
    match projectee with | { uenv; names; names_t; module_name;_} -> uenv
let (__proj__Mkenv__item__names : env -> name Prims.list) =
  fun projectee ->
    match projectee with | { uenv; names; names_t; module_name;_} -> names
let (__proj__Mkenv__item__names_t : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { uenv; names; names_t; module_name;_} -> names_t
let (__proj__Mkenv__item__module_name : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { uenv; names; names_t; module_name;_} -> module_name
let (__proj__Mkname__item__pretty : name -> Prims.string) =
  fun projectee -> match projectee with | { pretty;_} -> pretty
let (empty :
  FStarC_Extraction_ML_UEnv.uenv -> Prims.string Prims.list -> env) =
  fun uenv ->
    fun module_name -> { uenv; names = []; names_t = []; module_name }
let (extend : env -> Prims.string -> env) =
  fun env1 ->
    fun x ->
      {
        uenv = (env1.uenv);
        names = ({ pretty = x } :: (env1.names));
        names_t = (env1.names_t);
        module_name = (env1.module_name)
      }
let (extend_t : env -> Prims.string -> env) =
  fun env1 ->
    fun x ->
      {
        uenv = (env1.uenv);
        names = (env1.names);
        names_t = (x :: (env1.names_t));
        module_name = (env1.module_name)
      }
let (find_name : env -> Prims.string -> name) =
  fun env1 ->
    fun x ->
      let uu___ =
        FStarC_Compiler_List.tryFind (fun name1 -> name1.pretty = x)
          env1.names in
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
               FStarC_Compiler_List.index (fun name1 -> name1.pretty = x)
                 env1.names) ()
      with
      | uu___ ->
          let uu___1 =
            FStarC_Compiler_Util.format1
              "Internal error: name not found %s\n" x in
          failwith uu___1
let (find_t : env -> Prims.string -> Prims.int) =
  fun env1 ->
    fun x ->
      try
        (fun uu___ ->
           match () with
           | () ->
               FStarC_Compiler_List.index (fun name1 -> name1 = x)
                 env1.names_t) ()
      with
      | uu___ ->
          let uu___1 =
            FStarC_Compiler_Util.format1
              "Internal error: name not found %s\n" x in
          failwith uu___1
let (add_binders :
  env -> FStarC_Extraction_ML_Syntax.mlbinder Prims.list -> env) =
  fun env1 ->
    fun bs ->
      FStarC_Compiler_List.fold_left
        (fun env2 ->
           fun uu___ ->
             match uu___ with
             | { FStarC_Extraction_ML_Syntax.mlbinder_name = mlbinder_name;
                 FStarC_Extraction_ML_Syntax.mlbinder_ty = uu___1;
                 FStarC_Extraction_ML_Syntax.mlbinder_attrs = uu___2;_} ->
                 extend env2 mlbinder_name) env1 bs
let (list_elements :
  FStarC_Extraction_ML_Syntax.mlexpr ->
    FStarC_Extraction_ML_Syntax.mlexpr Prims.list)
  =
  fun e ->
    let lopt = FStarC_Extraction_ML_Util.list_elements e in
    match lopt with
    | FStar_Pervasives_Native.None ->
        failwith "Argument of FStar.Buffer.createL is not a list literal!"
    | FStar_Pervasives_Native.Some l -> l
let (translate_flags :
  FStarC_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags ->
    FStarC_Compiler_List.choose
      (fun uu___ ->
         match uu___ with
         | FStarC_Extraction_ML_Syntax.Private ->
             FStar_Pervasives_Native.Some Private
         | FStarC_Extraction_ML_Syntax.NoExtract ->
             FStar_Pervasives_Native.Some WipeBody
         | FStarC_Extraction_ML_Syntax.CInline ->
             FStar_Pervasives_Native.Some CInline
         | FStarC_Extraction_ML_Syntax.CNoInline ->
             FStar_Pervasives_Native.Some CNoInline
         | FStarC_Extraction_ML_Syntax.Substitute ->
             FStar_Pervasives_Native.Some Substitute
         | FStarC_Extraction_ML_Syntax.GCType ->
             FStar_Pervasives_Native.Some GCType
         | FStarC_Extraction_ML_Syntax.Comment s ->
             FStar_Pervasives_Native.Some (Comment s)
         | FStarC_Extraction_ML_Syntax.StackInline ->
             FStar_Pervasives_Native.Some MustDisappear
         | FStarC_Extraction_ML_Syntax.CConst s ->
             FStar_Pervasives_Native.Some (Const s)
         | FStarC_Extraction_ML_Syntax.CPrologue s ->
             FStar_Pervasives_Native.Some (Prologue s)
         | FStarC_Extraction_ML_Syntax.CEpilogue s ->
             FStar_Pervasives_Native.Some (Epilogue s)
         | FStarC_Extraction_ML_Syntax.CAbstract ->
             FStar_Pervasives_Native.Some Abstract
         | FStarC_Extraction_ML_Syntax.CIfDef ->
             FStar_Pervasives_Native.Some IfDef
         | FStarC_Extraction_ML_Syntax.CMacro ->
             FStar_Pervasives_Native.Some Macro
         | FStarC_Extraction_ML_Syntax.Deprecated s ->
             FStar_Pervasives_Native.Some (Deprecated s)
         | uu___1 -> FStar_Pervasives_Native.None) flags
let (translate_cc :
  FStarC_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags ->
    let uu___ =
      FStarC_Compiler_List.choose
        (fun uu___1 ->
           match uu___1 with
           | FStarC_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu___2 -> FStar_Pervasives_Native.None) flags in
    match uu___ with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu___1 -> FStar_Pervasives_Native.None
let (generate_is_null : typ -> expr -> expr) =
  fun t ->
    fun x ->
      let dummy = UInt64 in
      EApp ((ETypApp ((EOp (Eq, dummy)), [TBuf t])), [x; EBufNull t])
exception NotSupportedByKrmlExtension 
let (uu___is_NotSupportedByKrmlExtension : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | NotSupportedByKrmlExtension -> true
    | uu___ -> false
type translate_type_without_decay_t =
  env -> FStarC_Extraction_ML_Syntax.mlty -> typ
let (ref_translate_type_without_decay :
  translate_type_without_decay_t FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref
    (fun uu___ ->
       fun uu___1 -> FStarC_Compiler_Effect.raise NotSupportedByKrmlExtension)
let (register_pre_translate_type_without_decay :
  translate_type_without_decay_t -> unit) =
  fun f ->
    let before =
      FStarC_Compiler_Effect.op_Bang ref_translate_type_without_decay in
    let after e t =
      try (fun uu___ -> match () with | () -> f e t) ()
      with | NotSupportedByKrmlExtension -> before e t in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_type_without_decay
      after
let (register_post_translate_type_without_decay :
  translate_type_without_decay_t -> unit) =
  fun f ->
    let before =
      FStarC_Compiler_Effect.op_Bang ref_translate_type_without_decay in
    let after e t =
      try (fun uu___ -> match () with | () -> before e t) ()
      with | NotSupportedByKrmlExtension -> f e t in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_type_without_decay
      after
let (translate_type_without_decay :
  env -> FStarC_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 ->
    fun t ->
      let uu___ =
        FStarC_Compiler_Effect.op_Bang ref_translate_type_without_decay in
      uu___ env1 t
type translate_type_t = env -> FStarC_Extraction_ML_Syntax.mlty -> typ
let (ref_translate_type : translate_type_t FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref
    (fun uu___ ->
       fun uu___1 -> FStarC_Compiler_Effect.raise NotSupportedByKrmlExtension)
let (register_pre_translate_type : translate_type_t -> unit) =
  fun f ->
    let before = FStarC_Compiler_Effect.op_Bang ref_translate_type in
    let after e t =
      try (fun uu___ -> match () with | () -> f e t) ()
      with | NotSupportedByKrmlExtension -> before e t in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_type after
let (register_post_translate_type : translate_type_t -> unit) =
  fun f ->
    let before = FStarC_Compiler_Effect.op_Bang ref_translate_type in
    let after e t =
      try (fun uu___ -> match () with | () -> before e t) ()
      with | NotSupportedByKrmlExtension -> f e t in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_type after
let (translate_type : env -> FStarC_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 ->
    fun t ->
      let uu___ = FStarC_Compiler_Effect.op_Bang ref_translate_type in
      uu___ env1 t
type translate_expr_t = env -> FStarC_Extraction_ML_Syntax.mlexpr -> expr
let (ref_translate_expr : translate_expr_t FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref
    (fun uu___ ->
       fun uu___1 -> FStarC_Compiler_Effect.raise NotSupportedByKrmlExtension)
let (register_pre_translate_expr : translate_expr_t -> unit) =
  fun f ->
    let before = FStarC_Compiler_Effect.op_Bang ref_translate_expr in
    let after e t =
      try (fun uu___ -> match () with | () -> f e t) ()
      with | NotSupportedByKrmlExtension -> before e t in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_expr after
let (register_post_translate_expr : translate_expr_t -> unit) =
  fun f ->
    let before = FStarC_Compiler_Effect.op_Bang ref_translate_expr in
    let after e t =
      try (fun uu___ -> match () with | () -> before e t) ()
      with | NotSupportedByKrmlExtension -> f e t in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_expr after
let (translate_expr : env -> FStarC_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env1 ->
    fun e ->
      let uu___ = FStarC_Compiler_Effect.op_Bang ref_translate_expr in
      uu___ env1 e
type translate_type_decl_t =
  env ->
    FStarC_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option
let (ref_translate_type_decl :
  translate_type_decl_t FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref
    (fun uu___ ->
       fun uu___1 -> FStarC_Compiler_Effect.raise NotSupportedByKrmlExtension)
let (register_pre_translate_type_decl : translate_type_decl_t -> unit) =
  fun f ->
    let before = FStarC_Compiler_Effect.op_Bang ref_translate_type_decl in
    let after e t =
      try (fun uu___ -> match () with | () -> f e t) ()
      with | NotSupportedByKrmlExtension -> before e t in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_type_decl after
let (register_post_translate_type_decl : translate_type_decl_t -> unit) =
  fun f ->
    let before = FStarC_Compiler_Effect.op_Bang ref_translate_type_decl in
    let after e t =
      try (fun uu___ -> match () with | () -> before e t) ()
      with | NotSupportedByKrmlExtension -> f e t in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_type_decl after
let (translate_type_decl :
  env ->
    FStarC_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ty ->
      if
        FStarC_Compiler_List.mem FStarC_Extraction_ML_Syntax.NoExtract
          ty.FStarC_Extraction_ML_Syntax.tydecl_meta
      then FStar_Pervasives_Native.None
      else
        (let uu___1 = FStarC_Compiler_Effect.op_Bang ref_translate_type_decl in
         uu___1 env1 ty)
let rec (translate_type_without_decay' :
  env -> FStarC_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 ->
    fun t ->
      match t with
      | FStarC_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStarC_Extraction_ML_Syntax.MLTY_Top -> TAny
      | FStarC_Extraction_ML_Syntax.MLTY_Var name1 ->
          let uu___ = find_t env1 name1 in TBound uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
          let uu___1 =
            let uu___2 = translate_type_without_decay env1 t1 in
            let uu___3 = translate_type_without_decay env1 t2 in
            (uu___2, uu___3) in
          TArrow uu___1
      | FStarC_Extraction_ML_Syntax.MLTY_Erased -> TUnit
      | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Prims.unit" -> TUnit
      | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "Prims.bool" -> TBool
      | FStarC_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t"))
          when is_machine_int m ->
          let uu___ = FStarC_Compiler_Util.must (mk_width m) in TInt uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t'"))
          when is_machine_int m ->
          let uu___ = FStarC_Compiler_Util.must (mk_width m) in TInt uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStarC_Extraction_ML_Syntax.MLTY_Named (uu___::arg::uu___1::[], p)
          when
          (((let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___2 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___2 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___2 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___2 = "FStar.HyperStack.ST.s_mref")
          ->
          let uu___2 = translate_type_without_decay env1 arg in TBuf uu___2
      | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::uu___::[], p) when
          ((((((((((let uu___1 =
                      FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                    uu___1 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu___1 =
                        FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                      uu___1 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu___1 =
                       FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                     uu___1 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu___1 =
                      FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                    uu___1 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu___1 =
                     FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                   uu___1 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___1 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___1 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___1 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___1 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___1 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___1 = "FStar.HyperStack.ST.mmmref")
          ->
          let uu___1 = translate_type_without_decay env1 arg in TBuf uu___1
      | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::uu___::uu___1::[], p)
          when
          let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu___2 = translate_type_without_decay env1 arg in TBuf uu___2
      | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          (let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___ = "LowStar.ConstBuffer.const_buffer") || false
          ->
          let uu___ = translate_type_without_decay env1 arg in
          TConstBuf uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          ((((((((((((((let uu___ =
                          FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                        uu___ = "FStar.Buffer.buffer") ||
                         (let uu___ =
                            FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                          uu___ = "LowStar.Buffer.buffer"))
                        ||
                        (let uu___ =
                           FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                         uu___ = "LowStar.ImmutableBuffer.ibuffer"))
                       ||
                       (let uu___ =
                          FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                        uu___ = "LowStar.UninitializedBuffer.ubuffer"))
                      ||
                      (let uu___ =
                         FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                       uu___ = "FStar.HyperStack.reference"))
                     ||
                     (let uu___ =
                        FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                      uu___ = "FStar.HyperStack.stackref"))
                    ||
                    (let uu___ =
                       FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                     uu___ = "FStar.HyperStack.ref"))
                   ||
                   (let uu___ =
                      FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                    uu___ = "FStar.HyperStack.mmstackref"))
                  ||
                  (let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                   uu___ = "FStar.HyperStack.mmref"))
                 ||
                 (let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                  uu___ = "FStar.HyperStack.ST.reference"))
                ||
                (let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___ = "FStar.HyperStack.ST.stackref"))
               ||
               (let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___ = "FStar.HyperStack.ST.ref"))
              ||
              (let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___ = "FStar.HyperStack.ST.mmstackref"))
             ||
             (let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___ = "FStar.HyperStack.ST.mmref"))
            || false
          -> let uu___ = translate_type_without_decay env1 arg in TBuf uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Named (uu___::arg::[], p) when
          (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___1 = "FStar.HyperStack.s_ref") ||
            (let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___1 = "FStar.HyperStack.ST.s_ref")
          ->
          let uu___1 = translate_type_without_decay env1 arg in TBuf uu___1
      | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___ = "FStar.Universe.raise_t" ->
          translate_type_without_decay env1 arg
      | FStarC_Extraction_ML_Syntax.MLTY_Named (uu___::[], p) when
          let uu___1 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___1 = "FStar.Ghost.erased" -> TAny
      | FStarC_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) ->
          TQualified (path, type_name)
      | FStarC_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStarC_Compiler_Util.starts_with t1 "tuple")
          ->
          let uu___ =
            FStarC_Compiler_List.map (translate_type_without_decay env1) args in
          TTuple uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Named (args, lid) ->
          if (FStarC_Compiler_List.length args) > Prims.int_zero
          then
            let uu___ =
              let uu___1 =
                FStarC_Compiler_List.map (translate_type_without_decay env1)
                  args in
              (lid, uu___1) in
            TApp uu___
          else TQualified lid
      | FStarC_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu___ =
            FStarC_Compiler_List.map (translate_type_without_decay env1) ts in
          TTuple uu___
and (translate_type' : env -> FStarC_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 -> fun t -> translate_type_without_decay env1 t
and (translate_binders :
  env -> FStarC_Extraction_ML_Syntax.mlbinder Prims.list -> binder Prims.list)
  = fun env1 -> fun bs -> FStarC_Compiler_List.map (translate_binder env1) bs
and (translate_binder :
  env -> FStarC_Extraction_ML_Syntax.mlbinder -> binder) =
  fun env1 ->
    fun uu___ ->
      match uu___ with
      | { FStarC_Extraction_ML_Syntax.mlbinder_name = mlbinder_name;
          FStarC_Extraction_ML_Syntax.mlbinder_ty = mlbinder_ty;
          FStarC_Extraction_ML_Syntax.mlbinder_attrs = mlbinder_attrs;_} ->
          let uu___1 = translate_type env1 mlbinder_ty in
          { name = mlbinder_name; typ = uu___1; mut = false; meta = [] }
and (translate_expr' : env -> FStarC_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env1 ->
    fun e ->
      match e.FStarC_Extraction_ML_Syntax.expr with
      | FStarC_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStarC_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStarC_Extraction_ML_Syntax.MLE_Var name1 ->
          let uu___ = find env1 name1 in EBound uu___
      | FStarC_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op1) when
          (is_machine_int m) && (is_op op1) ->
          let uu___ =
            let uu___1 = FStarC_Compiler_Util.must (mk_op op1) in
            let uu___2 = FStarC_Compiler_Util.must (mk_width m) in
            (uu___1, uu___2) in
          EOp uu___
      | FStarC_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op1) when
          is_bool_op op1 ->
          let uu___ =
            let uu___1 = FStarC_Compiler_Util.must (mk_bool_op op1) in
            (uu___1, Bool) in
          EOp uu___
      | FStarC_Extraction_ML_Syntax.MLE_Name n -> EQualified n
      | FStarC_Extraction_ML_Syntax.MLE_Let
          ((flavor,
            { FStarC_Extraction_ML_Syntax.mllb_name = name1;
              FStarC_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some ([], typ1);
              FStarC_Extraction_ML_Syntax.mllb_add_unit = add_unit;
              FStarC_Extraction_ML_Syntax.mllb_def = body;
              FStarC_Extraction_ML_Syntax.mllb_attrs = uu___;
              FStarC_Extraction_ML_Syntax.mllb_meta = flags;
              FStarC_Extraction_ML_Syntax.print_typ = print;_}::[]),
           continuation)
          ->
          let binder1 =
            let uu___1 = translate_type env1 typ1 in
            let uu___2 = translate_flags flags in
            { name = name1; typ = uu___1; mut = false; meta = uu___2 } in
          let body1 = translate_expr env1 body in
          let env2 = extend env1 name1 in
          let continuation1 = translate_expr env2 continuation in
          ELet (binder1, body1, continuation1)
      | FStarC_Extraction_ML_Syntax.MLE_Match (expr1, branches1) ->
          let uu___ =
            let uu___1 = translate_expr env1 expr1 in
            let uu___2 = translate_branches env1 branches1 in
            (uu___1, uu___2) in
          EMatch uu___
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_},
           arg::[])
          when
          let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___4 = "FStarC.Dyn.undyn" ->
          let uu___4 =
            let uu___5 = translate_expr env1 arg in
            let uu___6 = translate_type env1 t in (uu___5, uu___6) in
          ECast uu___4
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5)
          when
          let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "Prims.admit" -> EAbort
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_},
           {
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_String s);
             FStarC_Extraction_ML_Syntax.mlty = uu___4;
             FStarC_Extraction_ML_Syntax.loc = uu___5;_}::[])
          when
          let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___6 = "LowStar.Failure.failwith" ->
          let uu___6 = let uu___7 = translate_type env1 t in (s, uu___7) in
          EAbortT uu___6
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           arg::[])
          when
          ((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.HyperStack.All.failwith") ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "FStar.Error.unexpected"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStarC_Extraction_ML_Syntax.expr =
                 FStarC_Extraction_ML_Syntax.MLE_Const
                 (FStarC_Extraction_ML_Syntax.MLC_String msg);
               FStarC_Extraction_ML_Syntax.mlty = uu___5;
               FStarC_Extraction_ML_Syntax.loc = uu___6;_} -> EAbortS msg
           | uu___5 ->
               let print_nm = (["FStar"; "HyperStack"; "IO"], "print_string") in
               let print =
                 FStarC_Extraction_ML_Syntax.with_ty
                   FStarC_Extraction_ML_Syntax.MLTY_Top
                   (FStarC_Extraction_ML_Syntax.MLE_Name print_nm) in
               let print1 =
                 FStarC_Extraction_ML_Syntax.with_ty
                   FStarC_Extraction_ML_Syntax.MLTY_Top
                   (FStarC_Extraction_ML_Syntax.MLE_App (print, [arg])) in
               let t = translate_expr env1 print1 in ESequence [t; EAbort])
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env1 e1
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          ((((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "FStar.Buffer.index") ||
               (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___5 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ConstBuffer.index")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufRead uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.HyperStack.ST.op_Bang" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            (uu___6, (EQualified (["C"], "_zero_for_deref"))) in
          EBufRead uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           arg::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.Universe.raise_val" -> translate_expr env1 arg
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           arg::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.Universe.downgrade_val" -> translate_expr env1 arg
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          ((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.create") ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (Stack, uu___6, uu___7) in
          EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           elen::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu___5 =
            let uu___6 = translate_expr env1 elen in (Stack, uu___6) in
          EBufCreateNoInit uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           init::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.salloc") || false
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 init in
            (Stack, uu___6, (EConstant (UInt32, "1"))) in
          EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e2::[])
          when
          ((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.createL") ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu___5 =
            let uu___6 =
              let uu___7 = list_elements e2 in
              FStarC_Compiler_List.map (translate_expr env1) uu___7 in
            (Stack, uu___6) in
          EBufCreateL uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _erid::e2::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu___5 =
            let uu___6 =
              let uu___7 = list_elements e2 in
              FStarC_Compiler_List.map (translate_expr env1) uu___7 in
            (Eternal, uu___6) in
          EBufCreateL uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _rid::init::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.ralloc") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.HyperStack.ST.ralloc_drgn")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 init in
            (Eternal, uu___6, (EConstant (UInt32, "1"))) in
          EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _e0::e1::e2::[])
          when
          ((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.rcreate") ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (Eternal, uu___6, uu___7) in
          EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           uu___5)
          when
          (((((let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___6 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___6 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
                uu___6 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___6 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___6 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu___6 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___6 = "LowStar.ImmutableBuffer.ialloca_and_blit")
          ->
          EAbortS
            "alloc_and_blit family of functions are not yet supported downstream"
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _erid::elen::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu___5 =
            let uu___6 = translate_expr env1 elen in (Eternal, uu___6) in
          EBufCreateNoInit uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _rid::init::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.ralloc_mm") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.HyperStack.ST.ralloc_drgn_mm")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 init in
            (ManuallyManaged, uu___6, (EConstant (UInt32, "1"))) in
          EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _e0::e1::e2::[])
          when
          (((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.Buffer.rcreate_mm") ||
              (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            (ManuallyManaged, uu___6, uu___7) in
          EBufCreate uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _erid::elen::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu___5 =
            let uu___6 = translate_expr env1 elen in
            (ManuallyManaged, uu___6) in
          EBufCreateNoInit uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e2::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.rfree") || false
          -> let uu___5 = translate_expr env1 e2 in EBufFree uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e2::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.Buffer.rfree") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.Monotonic.Buffer.free")
          -> let uu___5 = translate_expr env1 e2 in EBufFree uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::_e3::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.Buffer.sub" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufSub uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::_e3::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ConstBuffer.sub")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufSub uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.Buffer.join" -> translate_expr env1 e1
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.Buffer.offset" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufSub uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
          EBufSub uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::e3::[])
          when
          (((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.Buffer.upd") ||
              (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            let uu___8 = translate_expr env1 e3 in (uu___6, uu___7, uu___8) in
          EBufWrite uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::[])
          when
          let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___5 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            (uu___6, (EQualified (["C"], "_zero_for_deref")), uu___7) in
          EBufWrite uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2::[])
          when
          (let uu___3 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___3 = "FStar.HyperStack.ST.push_frame") || false
          -> EPushFrame
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2::[])
          when
          let uu___3 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___3 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::e3::e4::e5::[])
          when
          ((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___5 = "FStar.Buffer.blit") ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
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
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::e2::e3::[])
          when
          let s = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu___5 =
            let uu___6 = translate_expr env1 e1 in
            let uu___7 = translate_expr env1 e2 in
            let uu___8 = translate_expr env1 e3 in (uu___6, uu___7, uu___8) in
          EBufFill uu___5
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           uu___2::[])
          when
          let uu___3 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___3 = "FStar.HyperStack.ST.get" -> EUnit
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _rid::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "FStar.HyperStack.ST.free_drgn") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "FStar.HyperStack.ST.new_drgn")
          -> EUnit
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           _ebuf::_eseq::[])
          when
          (((let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___5 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___5 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           e1::[])
          when
          (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
           uu___5 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu___5 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___5 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env1 e1
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_},
           _eqal::e1::[])
          when
          let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___4 = "LowStar.ConstBuffer.of_qbuf" ->
          let uu___4 =
            let uu___5 = translate_expr env1 e1 in
            let uu___6 =
              let uu___7 = translate_type env1 t in TConstBuf uu___7 in
            (uu___5, uu___6) in
          ECast uu___4
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                t::[]);
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_},
           e1::[])
          when
          ((let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
            uu___4 = "LowStar.ConstBuffer.cast") ||
             (let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___4 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___4 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu___4 =
            let uu___5 = translate_expr env1 e1 in
            let uu___6 = let uu___7 = translate_type env1 t in TBuf uu___7 in
            (uu___5, uu___6) in
          ECast uu___4
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           e1::[])
          when
          let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "Obj.repr" ->
          let uu___2 = let uu___3 = translate_expr env1 e1 in (uu___3, TAny) in
          ECast uu___2
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op1);
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           args)
          when (is_machine_int m) && (is_op op1) ->
          let uu___2 = FStarC_Compiler_Util.must (mk_width m) in
          let uu___3 = FStarC_Compiler_Util.must (mk_op op1) in
          mk_op_app env1 uu___2 uu___3 args
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op1);
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           args)
          when is_bool_op op1 ->
          let uu___2 = FStarC_Compiler_Util.must (mk_bool_op op1) in
          mk_op_app env1 Bool uu___2 args
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "int_to_t");
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           {
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
          when is_machine_int m ->
          let uu___4 =
            let uu___5 = FStarC_Compiler_Util.must (mk_width m) in
            (uu___5, c) in
          EConstant uu___4
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "uint_to_t");
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           {
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
          when is_machine_int m ->
          let uu___4 =
            let uu___5 = FStarC_Compiler_Util.must (mk_width m) in
            (uu___5, c) in
          EConstant uu___4
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name
               ("C"::[], "string_of_literal");
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           { FStarC_Extraction_ML_Syntax.expr = e1;
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
          ->
          (match e1 with
           | FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu___4 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[], "of_literal");
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           { FStarC_Extraction_ML_Syntax.expr = e1;
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
          ->
          (match e1 with
           | FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu___4 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[], "of_literal");
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           { FStarC_Extraction_ML_Syntax.expr = e1;
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
          ->
          (match e1 with
           | FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu___4 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStarC_Extraction_ML_Syntax.expr =
                    FStarC_Extraction_ML_Syntax.MLE_Name p;
                  FStarC_Extraction_ML_Syntax.mlty = uu___;
                  FStarC_Extraction_ML_Syntax.loc = uu___1;_},
                uu___2);
             FStarC_Extraction_ML_Syntax.mlty = uu___3;
             FStarC_Extraction_ML_Syntax.loc = uu___4;_},
           { FStarC_Extraction_ML_Syntax.expr = ebefore;
             FStarC_Extraction_ML_Syntax.mlty = uu___5;
             FStarC_Extraction_ML_Syntax.loc = uu___6;_}::e1::{
                                                                FStarC_Extraction_ML_Syntax.expr
                                                                  = eafter;
                                                                FStarC_Extraction_ML_Syntax.mlty
                                                                  = uu___7;
                                                                FStarC_Extraction_ML_Syntax.loc
                                                                  = uu___8;_}::[])
          when
          let uu___9 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___9 = "LowStar.Comment.comment_gen" ->
          (match (ebefore, eafter) with
           | (FStarC_Extraction_ML_Syntax.MLE_Const
              (FStarC_Extraction_ML_Syntax.MLC_String sbefore),
              FStarC_Extraction_ML_Syntax.MLE_Const
              (FStarC_Extraction_ML_Syntax.MLC_String safter)) ->
               (if FStarC_Compiler_Util.contains sbefore "*/"
                then failwith "Before Comment contains end-of-comment marker"
                else ();
                if FStarC_Compiler_Util.contains safter "*/"
                then failwith "After Comment contains end-of-comment marker"
                else ();
                (let uu___11 =
                   let uu___12 = translate_expr env1 e1 in
                   (sbefore, uu___12, safter) in
                 EComment uu___11))
           | uu___9 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           { FStarC_Extraction_ML_Syntax.expr = e1;
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
          when
          let uu___4 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___4 = "LowStar.Comment.comment" ->
          (match e1 with
           | FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_String s) ->
               (if FStarC_Compiler_Util.contains s "*/"
                then
                  failwith
                    "Standalone Comment contains end-of-comment marker"
                else ();
                EStandaloneComment s)
           | uu___4 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[], "buffer_of_literal");
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           { FStarC_Extraction_ML_Syntax.expr = e1;
             FStarC_Extraction_ML_Syntax.mlty = uu___2;
             FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
          ->
          (match e1 with
           | FStarC_Extraction_ML_Syntax.MLE_Const
               (FStarC_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu___4 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[], c);
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           arg::[])
          ->
          let is_known_type =
            (((((((FStarC_Compiler_Util.starts_with c "uint8") ||
                    (FStarC_Compiler_Util.starts_with c "uint16"))
                   || (FStarC_Compiler_Util.starts_with c "uint32"))
                  || (FStarC_Compiler_Util.starts_with c "uint64"))
                 || (FStarC_Compiler_Util.starts_with c "int8"))
                || (FStarC_Compiler_Util.starts_with c "int16"))
               || (FStarC_Compiler_Util.starts_with c "int32"))
              || (FStarC_Compiler_Util.starts_with c "int64") in
          if (FStarC_Compiler_Util.ends_with c "uint64") && is_known_type
          then
            let uu___2 =
              let uu___3 = translate_expr env1 arg in (uu___3, (TInt UInt64)) in
            ECast uu___2
          else
            if (FStarC_Compiler_Util.ends_with c "uint32") && is_known_type
            then
              (let uu___3 =
                 let uu___4 = translate_expr env1 arg in
                 (uu___4, (TInt UInt32)) in
               ECast uu___3)
            else
              if (FStarC_Compiler_Util.ends_with c "uint16") && is_known_type
              then
                (let uu___4 =
                   let uu___5 = translate_expr env1 arg in
                   (uu___5, (TInt UInt16)) in
                 ECast uu___4)
              else
                if
                  (FStarC_Compiler_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu___5 =
                     let uu___6 = translate_expr env1 arg in
                     (uu___6, (TInt UInt8)) in
                   ECast uu___5)
                else
                  if
                    (FStarC_Compiler_Util.ends_with c "int64") &&
                      is_known_type
                  then
                    (let uu___6 =
                       let uu___7 = translate_expr env1 arg in
                       (uu___7, (TInt Int64)) in
                     ECast uu___6)
                  else
                    if
                      (FStarC_Compiler_Util.ends_with c "int32") &&
                        is_known_type
                    then
                      (let uu___7 =
                         let uu___8 = translate_expr env1 arg in
                         (uu___8, (TInt Int32)) in
                       ECast uu___7)
                    else
                      if
                        (FStarC_Compiler_Util.ends_with c "int16") &&
                          is_known_type
                      then
                        (let uu___8 =
                           let uu___9 = translate_expr env1 arg in
                           (uu___9, (TInt Int16)) in
                         ECast uu___8)
                      else
                        if
                          (FStarC_Compiler_Util.ends_with c "int8") &&
                            is_known_type
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
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           arg::[])
          when
          (((let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___2 = "FStar.SizeT.uint16_to_sizet") ||
              (let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
               uu___2 = "FStar.SizeT.uint32_to_sizet"))
             ||
             (let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
              uu___2 = "FStar.SizeT.uint64_to_sizet"))
            ||
            (let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
             uu___2 = "FStar.PtrdiffT.ptrdifft_to_sizet")
          ->
          let uu___2 =
            let uu___3 = translate_expr env1 arg in (uu___3, (TInt SizeT)) in
          ECast uu___2
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           arg::[])
          when
          let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "FStar.SizeT.sizet_to_uint32" ->
          let uu___2 =
            let uu___3 = translate_expr env1 arg in (uu___3, (TInt UInt32)) in
          ECast uu___2
      | FStarC_Extraction_ML_Syntax.MLE_App
          ({
             FStarC_Extraction_ML_Syntax.expr =
               FStarC_Extraction_ML_Syntax.MLE_Name p;
             FStarC_Extraction_ML_Syntax.mlty = uu___;
             FStarC_Extraction_ML_Syntax.loc = uu___1;_},
           arg::[])
          when
          let uu___2 = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
          uu___2 = "FStar.SizeT.sizet_to_uint64" ->
          let uu___2 =
            let uu___3 = translate_expr env1 arg in (uu___3, (TInt UInt64)) in
          ECast uu___2
      | FStarC_Extraction_ML_Syntax.MLE_App (head, args) ->
          let uu___ =
            let uu___1 = translate_expr env1 head in
            let uu___2 = FStarC_Compiler_List.map (translate_expr env1) args in
            (uu___1, uu___2) in
          EApp uu___
      | FStarC_Extraction_ML_Syntax.MLE_TApp (head, ty_args) ->
          let uu___ =
            let uu___1 = translate_expr env1 head in
            let uu___2 =
              FStarC_Compiler_List.map (translate_type env1) ty_args in
            (uu___1, uu___2) in
          ETypApp uu___
      | FStarC_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) ->
          let uu___ =
            let uu___1 = translate_expr env1 e1 in
            let uu___2 = translate_type env1 t_to in (uu___1, uu___2) in
          ECast uu___
      | FStarC_Extraction_ML_Syntax.MLE_Record (uu___, uu___1, fields) ->
          let uu___2 =
            let uu___3 = assert_lid env1 e.FStarC_Extraction_ML_Syntax.mlty in
            let uu___4 =
              FStarC_Compiler_List.map
                (fun uu___5 ->
                   match uu___5 with
                   | (field, expr1) ->
                       let uu___6 = translate_expr env1 expr1 in
                       (field, uu___6)) fields in
            (uu___3, uu___4) in
          EFlat uu___2
      | FStarC_Extraction_ML_Syntax.MLE_Proj (e1, path) ->
          let uu___ =
            let uu___1 = assert_lid env1 e1.FStarC_Extraction_ML_Syntax.mlty in
            let uu___2 = translate_expr env1 e1 in
            (uu___1, uu___2, (FStar_Pervasives_Native.snd path)) in
          EField uu___
      | FStarC_Extraction_ML_Syntax.MLE_Let uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Extraction_ML_Code.string_of_mlexpr ([], "") e in
            FStarC_Compiler_Util.format1
              "todo: translate_expr [MLE_Let] (expr is: %s)" uu___2 in
          failwith uu___1
      | FStarC_Extraction_ML_Syntax.MLE_App (head, uu___) ->
          let uu___1 =
            let uu___2 =
              FStarC_Extraction_ML_Code.string_of_mlexpr ([], "") head in
            FStarC_Compiler_Util.format1
              "todo: translate_expr [MLE_App] (head is: %s)" uu___2 in
          failwith uu___1
      | FStarC_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu___ = FStarC_Compiler_List.map (translate_expr env1) seqs in
          ESequence uu___
      | FStarC_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu___ = FStarC_Compiler_List.map (translate_expr env1) es in
          ETuple uu___
      | FStarC_Extraction_ML_Syntax.MLE_CTor ((uu___, cons), es) ->
          let uu___1 =
            let uu___2 = assert_lid env1 e.FStarC_Extraction_ML_Syntax.mlty in
            let uu___3 = FStarC_Compiler_List.map (translate_expr env1) es in
            (uu___2, cons, uu___3) in
          ECons uu___1
      | FStarC_Extraction_ML_Syntax.MLE_Fun (bs, body) ->
          let binders = translate_binders env1 bs in
          let env2 = add_binders env1 bs in
          let uu___ =
            let uu___1 = translate_expr env2 body in
            let uu___2 =
              translate_type env2 body.FStarC_Extraction_ML_Syntax.mlty in
            (binders, uu___1, uu___2) in
          EFun uu___
      | FStarC_Extraction_ML_Syntax.MLE_If (e1, e2, e3) ->
          let uu___ =
            let uu___1 = translate_expr env1 e1 in
            let uu___2 = translate_expr env1 e2 in
            let uu___3 =
              match e3 with
              | FStar_Pervasives_Native.None -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env1 e31 in
            (uu___1, uu___2, uu___3) in
          EIfThenElse uu___
      | FStarC_Extraction_ML_Syntax.MLE_Raise uu___ ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStarC_Extraction_ML_Syntax.MLE_Try uu___ ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStarC_Extraction_ML_Syntax.MLE_Coerce uu___ ->
          failwith "todo: translate_expr [MLE_Coerce]"
and (assert_lid : env -> FStarC_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 ->
    fun t ->
      match t with
      | FStarC_Extraction_ML_Syntax.MLTY_Named (ts, lid) ->
          if (FStarC_Compiler_List.length ts) > Prims.int_zero
          then
            let uu___ =
              let uu___1 = FStarC_Compiler_List.map (translate_type env1) ts in
              (lid, uu___1) in
            TApp uu___
          else TQualified lid
      | uu___ ->
          let uu___1 =
            let uu___2 = FStarC_Extraction_ML_Code.string_of_mlty ([], "") t in
            FStarC_Compiler_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu___2 in
          failwith uu___1
and (translate_branches :
  env ->
    (FStarC_Extraction_ML_Syntax.mlpattern *
      FStarC_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option *
      FStarC_Extraction_ML_Syntax.mlexpr) Prims.list ->
      (pattern * expr) Prims.list)
  =
  fun env1 ->
    fun branches1 ->
      FStarC_Compiler_List.map (translate_branch env1) branches1
and (translate_branch :
  env ->
    (FStarC_Extraction_ML_Syntax.mlpattern *
      FStarC_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option *
      FStarC_Extraction_ML_Syntax.mlexpr) -> (pattern * expr))
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
  (FStarC_Const.signedness * FStarC_Const.width)
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> CInt
    | FStar_Pervasives_Native.Some (FStarC_Const.Signed, FStarC_Const.Int8)
        -> Int8
    | FStar_Pervasives_Native.Some (FStarC_Const.Signed, FStarC_Const.Int16)
        -> Int16
    | FStar_Pervasives_Native.Some (FStarC_Const.Signed, FStarC_Const.Int32)
        -> Int32
    | FStar_Pervasives_Native.Some (FStarC_Const.Signed, FStarC_Const.Int64)
        -> Int64
    | FStar_Pervasives_Native.Some (FStarC_Const.Unsigned, FStarC_Const.Int8)
        -> UInt8
    | FStar_Pervasives_Native.Some
        (FStarC_Const.Unsigned, FStarC_Const.Int16) -> UInt16
    | FStar_Pervasives_Native.Some
        (FStarC_Const.Unsigned, FStarC_Const.Int32) -> UInt32
    | FStar_Pervasives_Native.Some
        (FStarC_Const.Unsigned, FStarC_Const.Int64) -> UInt64
    | FStar_Pervasives_Native.Some
        (FStarC_Const.Unsigned, FStarC_Const.Sizet) -> SizeT
and (translate_pat :
  env -> FStarC_Extraction_ML_Syntax.mlpattern -> (env * pattern)) =
  fun env1 ->
    fun p ->
      match p with
      | FStarC_Extraction_ML_Syntax.MLP_Const
          (FStarC_Extraction_ML_Syntax.MLC_Unit) -> (env1, PUnit)
      | FStarC_Extraction_ML_Syntax.MLP_Const
          (FStarC_Extraction_ML_Syntax.MLC_Bool b) -> (env1, (PBool b))
      | FStarC_Extraction_ML_Syntax.MLP_Const
          (FStarC_Extraction_ML_Syntax.MLC_Int (s, sw)) ->
          let uu___ =
            let uu___1 = let uu___2 = translate_width sw in (uu___2, s) in
            PConstant uu___1 in
          (env1, uu___)
      | FStarC_Extraction_ML_Syntax.MLP_Var name1 ->
          let env2 = extend env1 name1 in
          (env2, (PVar { name = name1; typ = TAny; mut = false; meta = [] }))
      | FStarC_Extraction_ML_Syntax.MLP_Wild ->
          let env2 = extend env1 "_" in
          (env2, (PVar { name = "_"; typ = TAny; mut = false; meta = [] }))
      | FStarC_Extraction_ML_Syntax.MLP_CTor ((uu___, cons), ps) ->
          let uu___1 =
            FStarC_Compiler_List.fold_left
              (fun uu___2 ->
                 fun p1 ->
                   match uu___2 with
                   | (env2, acc) ->
                       let uu___3 = translate_pat env2 p1 in
                       (match uu___3 with | (env3, p2) -> (env3, (p2 :: acc))))
              (env1, []) ps in
          (match uu___1 with
           | (env2, ps1) ->
               (env2, (PCons (cons, (FStarC_Compiler_List.rev ps1)))))
      | FStarC_Extraction_ML_Syntax.MLP_Record (uu___, ps) ->
          let uu___1 =
            FStarC_Compiler_List.fold_left
              (fun uu___2 ->
                 fun uu___3 ->
                   match (uu___2, uu___3) with
                   | ((env2, acc), (field, p1)) ->
                       let uu___4 = translate_pat env2 p1 in
                       (match uu___4 with
                        | (env3, p2) -> (env3, ((field, p2) :: acc))))
              (env1, []) ps in
          (match uu___1 with
           | (env2, ps1) -> (env2, (PRecord (FStarC_Compiler_List.rev ps1))))
      | FStarC_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu___ =
            FStarC_Compiler_List.fold_left
              (fun uu___1 ->
                 fun p1 ->
                   match uu___1 with
                   | (env2, acc) ->
                       let uu___2 = translate_pat env2 p1 in
                       (match uu___2 with | (env3, p2) -> (env3, (p2 :: acc))))
              (env1, []) ps in
          (match uu___ with
           | (env2, ps1) -> (env2, (PTuple (FStarC_Compiler_List.rev ps1))))
      | FStarC_Extraction_ML_Syntax.MLP_Const uu___ ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStarC_Extraction_ML_Syntax.MLP_Branch uu___ ->
          failwith "todo: translate_pat [MLP_Branch]"
and (translate_constant : FStarC_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c ->
    match c with
    | FStarC_Extraction_ML_Syntax.MLC_Unit -> EUnit
    | FStarC_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStarC_Extraction_ML_Syntax.MLC_String s ->
        ((let uu___1 =
            FStarC_Compiler_Util.for_some
              (fun c1 -> c1 = (FStar_Char.char_of_int Prims.int_zero))
              (FStar_String.list_of_string s) in
          if uu___1
          then
            let uu___2 =
              FStarC_Compiler_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu___2
          else ());
         EString s)
    | FStarC_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStarC_Compiler_Util.int_of_char c1 in
        let s = FStarC_Compiler_Util.string_of_int i in
        let c2 = EConstant (CInt, s) in
        let char_of_int = EQualified (["FStar"; "Char"], "char_of_int") in
        EApp (char_of_int, [c2])
    | FStarC_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some (sg, wd)) ->
        let uu___ =
          let uu___1 =
            translate_width (FStar_Pervasives_Native.Some (sg, wd)) in
          (uu___1, s) in
        EConstant uu___
    | FStarC_Extraction_ML_Syntax.MLC_Float uu___ ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStarC_Extraction_ML_Syntax.MLC_Bytes uu___ ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStarC_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None)
        -> EConstant (CInt, s)
and (mk_op_app :
  env -> width -> op -> FStarC_Extraction_ML_Syntax.mlexpr Prims.list -> expr)
  =
  fun env1 ->
    fun w ->
      fun op1 ->
        fun args ->
          let uu___ =
            let uu___1 = FStarC_Compiler_List.map (translate_expr env1) args in
            ((EOp (op1, w)), uu___1) in
          EApp uu___
let (translate_type_decl' :
  env ->
    FStarC_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ty ->
      match ty with
      | { FStarC_Extraction_ML_Syntax.tydecl_assumed = assumed;
          FStarC_Extraction_ML_Syntax.tydecl_name = name1;
          FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___;
          FStarC_Extraction_ML_Syntax.tydecl_parameters = args;
          FStarC_Extraction_ML_Syntax.tydecl_meta = flags;
          FStarC_Extraction_ML_Syntax.tydecl_defn =
            FStar_Pervasives_Native.Some
            (FStarC_Extraction_ML_Syntax.MLTD_Abbrev t);_}
          ->
          let name2 = ((env1.module_name), name1) in
          let env2 =
            FStarC_Compiler_List.fold_left
              (fun env3 ->
                 fun uu___1 ->
                   match uu___1 with
                   | {
                       FStarC_Extraction_ML_Syntax.ty_param_name =
                         ty_param_name;
                       FStarC_Extraction_ML_Syntax.ty_param_attrs = uu___2;_}
                       -> extend_t env3 ty_param_name) env1 args in
          if
            assumed &&
              (FStarC_Compiler_List.mem FStarC_Extraction_ML_Syntax.CAbstract
                 flags)
          then FStar_Pervasives_Native.Some (DTypeAbstractStruct name2)
          else
            if assumed
            then
              (let name3 = FStarC_Extraction_ML_Syntax.string_of_mlpath name2 in
               FStarC_Compiler_Util.print1_warning
                 "Not extracting type definition %s to KaRaMeL (assumed type)\n"
                 name3;
               FStar_Pervasives_Native.None)
            else
              (let uu___3 =
                 let uu___4 =
                   let uu___5 = translate_flags flags in
                   let uu___6 = translate_type env2 t in
                   (name2, uu___5, (FStarC_Compiler_List.length args),
                     uu___6) in
                 DTypeAlias uu___4 in
               FStar_Pervasives_Native.Some uu___3)
      | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___;
          FStarC_Extraction_ML_Syntax.tydecl_name = name1;
          FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___1;
          FStarC_Extraction_ML_Syntax.tydecl_parameters = args;
          FStarC_Extraction_ML_Syntax.tydecl_meta = flags;
          FStarC_Extraction_ML_Syntax.tydecl_defn =
            FStar_Pervasives_Native.Some
            (FStarC_Extraction_ML_Syntax.MLTD_Record fields);_}
          ->
          let name2 = ((env1.module_name), name1) in
          let env2 =
            FStarC_Compiler_List.fold_left
              (fun env3 ->
                 fun uu___2 ->
                   match uu___2 with
                   | {
                       FStarC_Extraction_ML_Syntax.ty_param_name =
                         ty_param_name;
                       FStarC_Extraction_ML_Syntax.ty_param_attrs = uu___3;_}
                       -> extend_t env3 ty_param_name) env1 args in
          let uu___2 =
            let uu___3 =
              let uu___4 = translate_flags flags in
              let uu___5 =
                FStarC_Compiler_List.map
                  (fun uu___6 ->
                     match uu___6 with
                     | (f, t) ->
                         let uu___7 =
                           let uu___8 = translate_type_without_decay env2 t in
                           (uu___8, false) in
                         (f, uu___7)) fields in
              (name2, uu___4, (FStarC_Compiler_List.length args), uu___5) in
            DTypeFlat uu___3 in
          FStar_Pervasives_Native.Some uu___2
      | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___;
          FStarC_Extraction_ML_Syntax.tydecl_name = name1;
          FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___1;
          FStarC_Extraction_ML_Syntax.tydecl_parameters = args;
          FStarC_Extraction_ML_Syntax.tydecl_meta = flags;
          FStarC_Extraction_ML_Syntax.tydecl_defn =
            FStar_Pervasives_Native.Some
            (FStarC_Extraction_ML_Syntax.MLTD_DType branches1);_}
          ->
          let name2 = ((env1.module_name), name1) in
          let flags1 = translate_flags flags in
          let env2 =
            let uu___2 = FStarC_Extraction_ML_Syntax.ty_param_names args in
            FStarC_Compiler_List.fold_left extend_t env1 uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_Compiler_List.map
                  (fun uu___5 ->
                     match uu___5 with
                     | (cons, ts) ->
                         let uu___6 =
                           FStarC_Compiler_List.map
                             (fun uu___7 ->
                                match uu___7 with
                                | (name3, t) ->
                                    let uu___8 =
                                      let uu___9 =
                                        translate_type_without_decay env2 t in
                                      (uu___9, false) in
                                    (name3, uu___8)) ts in
                         (cons, uu___6)) branches1 in
              (name2, flags1, (FStarC_Compiler_List.length args), uu___4) in
            DTypeVariant uu___3 in
          FStar_Pervasives_Native.Some uu___2
      | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___;
          FStarC_Extraction_ML_Syntax.tydecl_name = name1;
          FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___1;
          FStarC_Extraction_ML_Syntax.tydecl_parameters = uu___2;
          FStarC_Extraction_ML_Syntax.tydecl_meta = uu___3;
          FStarC_Extraction_ML_Syntax.tydecl_defn = uu___4;_} ->
          ((let uu___6 =
              let uu___7 =
                let uu___8 =
                  FStarC_Compiler_Util.format1
                    "Error extracting type definition %s to KaRaMeL." name1 in
                FStarC_Errors_Msg.text uu___8 in
              [uu___7] in
            FStarC_Errors.log_issue0
              FStarC_Errors_Codes.Warning_DefinitionNotTranslated ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___6));
           FStar_Pervasives_Native.None)
let (translate_let' :
  env ->
    FStarC_Extraction_ML_Syntax.mlletflavor ->
      FStarC_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun flavor ->
      fun lb ->
        match lb with
        | { FStarC_Extraction_ML_Syntax.mllb_name = name1;
            FStarC_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStarC_Extraction_ML_Syntax.mllb_def = e;
            FStarC_Extraction_ML_Syntax.mllb_attrs = uu___1;
            FStarC_Extraction_ML_Syntax.mllb_meta = meta;
            FStarC_Extraction_ML_Syntax.print_typ = uu___2;_} when
            FStarC_Compiler_Util.for_some
              (fun uu___3 ->
                 match uu___3 with
                 | FStarC_Extraction_ML_Syntax.Assumed -> true
                 | uu___4 -> false) meta
            ->
            let name2 = ((env1.module_name), name1) in
            let arg_names =
              match e.FStarC_Extraction_ML_Syntax.expr with
              | FStarC_Extraction_ML_Syntax.MLE_Fun (bs, uu___3) ->
                  FStarC_Compiler_List.map
                    (fun uu___4 ->
                       match uu___4 with
                       | {
                           FStarC_Extraction_ML_Syntax.mlbinder_name =
                             mlbinder_name;
                           FStarC_Extraction_ML_Syntax.mlbinder_ty = uu___5;
                           FStarC_Extraction_ML_Syntax.mlbinder_attrs =
                             uu___6;_}
                           -> mlbinder_name) bs
              | uu___3 -> [] in
            if (FStarC_Compiler_List.length tvars) = Prims.int_zero
            then
              let uu___3 =
                let uu___4 =
                  let uu___5 = translate_cc meta in
                  let uu___6 = translate_flags meta in
                  let uu___7 = translate_type env1 t0 in
                  (uu___5, uu___6, name2, uu___7, arg_names) in
                DExternal uu___4 in
              FStar_Pervasives_Native.Some uu___3
            else
              ((let uu___5 =
                  FStarC_Extraction_ML_Syntax.string_of_mlpath name2 in
                FStarC_Compiler_Util.print1_warning
                  "Not extracting %s to KaRaMeL (polymorphic assumes are not supported)\n"
                  uu___5);
               FStar_Pervasives_Native.None)
        | { FStarC_Extraction_ML_Syntax.mllb_name = name1;
            FStarC_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStarC_Extraction_ML_Syntax.mllb_def =
              {
                FStarC_Extraction_ML_Syntax.expr =
                  FStarC_Extraction_ML_Syntax.MLE_Fun (args, body);
                FStarC_Extraction_ML_Syntax.mlty = uu___1;
                FStarC_Extraction_ML_Syntax.loc = uu___2;_};
            FStarC_Extraction_ML_Syntax.mllb_attrs = uu___3;
            FStarC_Extraction_ML_Syntax.mllb_meta = meta;
            FStarC_Extraction_ML_Syntax.print_typ = uu___4;_} ->
            if
              FStarC_Compiler_List.mem FStarC_Extraction_ML_Syntax.NoExtract
                meta
            then FStar_Pervasives_Native.None
            else
              (let env2 =
                 if flavor = FStarC_Extraction_ML_Syntax.Rec
                 then extend env1 name1
                 else env1 in
               let env3 =
                 let uu___6 =
                   FStarC_Extraction_ML_Syntax.ty_param_names tvars in
                 FStarC_Compiler_List.fold_left
                   (fun env4 -> fun name2 -> extend_t env4 name2) env2 uu___6 in
               let rec find_return_type eff i uu___6 =
                 match uu___6 with
                 | FStarC_Extraction_ML_Syntax.MLTY_Fun (uu___7, eff1, t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t) in
               let name2 = ((env3.module_name), name1) in
               let uu___6 =
                 find_return_type FStarC_Extraction_ML_Syntax.E_PURE
                   (FStarC_Compiler_List.length args) t0 in
               match uu___6 with
               | (i, eff, t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction" in
                       let uu___8 =
                         FStarC_Extraction_ML_Syntax.string_of_mlpath name2 in
                       FStarC_Compiler_Util.print2_warning
                         "Not extracting %s to KaRaMeL (%s)\n" uu___8 msg)
                    else ();
                    (let t1 = translate_type env3 t in
                     let binders = translate_binders env3 args in
                     let env4 = add_binders env3 args in
                     let cc1 = translate_cc meta in
                     let meta1 =
                       match (eff, t1) with
                       | (FStarC_Extraction_ML_Syntax.E_ERASABLE, uu___8) ->
                           let uu___9 = translate_flags meta in MustDisappear
                             :: uu___9
                       | (FStarC_Extraction_ML_Syntax.E_PURE, TUnit) ->
                           let uu___8 = translate_flags meta in MustDisappear
                             :: uu___8
                       | uu___8 -> translate_flags meta in
                     try
                       (fun uu___8 ->
                          match () with
                          | () ->
                              let body1 = translate_expr env4 body in
                              FStar_Pervasives_Native.Some
                                (DFunction
                                   (cc1, meta1,
                                     (FStarC_Compiler_List.length tvars), t1,
                                     name2, binders, body1))) ()
                     with
                     | uu___8 ->
                         let msg = FStarC_Compiler_Util.print_exn uu___8 in
                         ((let uu___10 =
                             let uu___11 =
                               let uu___12 =
                                 let uu___13 =
                                   FStarC_Extraction_ML_Syntax.string_of_mlpath
                                     name2 in
                                 FStarC_Compiler_Util.format1
                                   "Error while extracting %s to KaRaMeL."
                                   uu___13 in
                               FStarC_Errors_Msg.text uu___12 in
                             let uu___12 =
                               let uu___13 =
                                 FStarC_Pprint.arbitrary_string msg in
                               [uu___13] in
                             uu___11 :: uu___12 in
                           FStarC_Errors.log_issue0
                             FStarC_Errors_Codes.Warning_FunctionNotExtacted
                             ()
                             (Obj.magic
                                FStarC_Errors_Msg.is_error_message_list_doc)
                             (Obj.magic uu___10));
                          (let msg1 =
                             Prims.strcat
                               "This function was not extracted:\n" msg in
                           FStar_Pervasives_Native.Some
                             (DFunction
                                (cc1, meta1,
                                  (FStarC_Compiler_List.length tvars), t1,
                                  name2, binders, (EAbortS msg1))))))))
        | { FStarC_Extraction_ML_Syntax.mllb_name = name1;
            FStarC_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t);
            FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStarC_Extraction_ML_Syntax.mllb_def = expr1;
            FStarC_Extraction_ML_Syntax.mllb_attrs = uu___1;
            FStarC_Extraction_ML_Syntax.mllb_meta = meta;
            FStarC_Extraction_ML_Syntax.print_typ = uu___2;_} ->
            if
              FStarC_Compiler_List.mem FStarC_Extraction_ML_Syntax.NoExtract
                meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = translate_flags meta in
               let env2 =
                 let uu___4 =
                   FStarC_Extraction_ML_Syntax.ty_param_names tvars in
                 FStarC_Compiler_List.fold_left
                   (fun env3 -> fun name2 -> extend_t env3 name2) env1 uu___4 in
               let t1 = translate_type env2 t in
               let name2 = ((env2.module_name), name1) in
               try
                 (fun uu___4 ->
                    match () with
                    | () ->
                        let expr2 = translate_expr env2 expr1 in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name2,
                               (FStarC_Compiler_List.length tvars), t1,
                               expr2))) ()
               with
               | uu___4 ->
                   ((let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             FStarC_Extraction_ML_Syntax.string_of_mlpath
                               name2 in
                           FStarC_Compiler_Util.format1
                             "Error extracting %s to KaRaMeL." uu___9 in
                         FStarC_Errors_Msg.text uu___8 in
                       let uu___8 =
                         let uu___9 =
                           let uu___10 =
                             FStarC_Compiler_Util.print_exn uu___4 in
                           FStarC_Pprint.arbitrary_string uu___10 in
                         [uu___9] in
                       uu___7 :: uu___8 in
                     FStarC_Errors.log_issue0
                       FStarC_Errors_Codes.Warning_DefinitionNotTranslated ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___6));
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name2, (FStarC_Compiler_List.length tvars),
                           t1, EAny))))
        | { FStarC_Extraction_ML_Syntax.mllb_name = name1;
            FStarC_Extraction_ML_Syntax.mllb_tysc = ts;
            FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
            FStarC_Extraction_ML_Syntax.mllb_def = uu___1;
            FStarC_Extraction_ML_Syntax.mllb_attrs = uu___2;
            FStarC_Extraction_ML_Syntax.mllb_meta = uu___3;
            FStarC_Extraction_ML_Syntax.print_typ = uu___4;_} ->
            ((let uu___6 =
                FStarC_Compiler_Util.format1 "Not extracting %s to KaRaMeL\n"
                  name1 in
              FStarC_Errors.log_issue0
                FStarC_Errors_Codes.Warning_DefinitionNotTranslated ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___6));
             (match ts with
              | FStar_Pervasives_Native.Some (tps, t) ->
                  let uu___7 =
                    let uu___8 =
                      FStarC_Extraction_ML_Syntax.ty_param_names tps in
                    FStarC_Compiler_String.concat ", " uu___8 in
                  let uu___8 =
                    FStarC_Extraction_ML_Code.string_of_mlty ([], "") t in
                  FStarC_Compiler_Util.print2
                    "Type scheme is: forall %s. %s\n" uu___7 uu___8
              | FStar_Pervasives_Native.None -> ());
             FStar_Pervasives_Native.None)
type translate_let_t =
  env ->
    FStarC_Extraction_ML_Syntax.mlletflavor ->
      FStarC_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option
let (ref_translate_let : translate_let_t FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref translate_let'
let (register_pre_translate_let : translate_let_t -> unit) =
  fun f ->
    let before = FStarC_Compiler_Effect.op_Bang ref_translate_let in
    let after e fl lb =
      try (fun uu___ -> match () with | () -> f e fl lb) ()
      with | NotSupportedByKrmlExtension -> before e fl lb in
    FStarC_Compiler_Effect.op_Colon_Equals ref_translate_let after
let (translate_let :
  env ->
    FStarC_Extraction_ML_Syntax.mlletflavor ->
      FStarC_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun flavor ->
      fun lb ->
        let uu___ = FStarC_Compiler_Effect.op_Bang ref_translate_let in
        uu___ env1 flavor lb
let (translate_decl :
  env -> FStarC_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env1 ->
    fun d ->
      match d.FStarC_Extraction_ML_Syntax.mlmodule1_m with
      | FStarC_Extraction_ML_Syntax.MLM_Let (flavor, lbs) ->
          FStarC_Compiler_List.choose (translate_let env1 flavor) lbs
      | FStarC_Extraction_ML_Syntax.MLM_Loc uu___ -> []
      | FStarC_Extraction_ML_Syntax.MLM_Ty tys ->
          FStarC_Compiler_List.choose (translate_type_decl env1) tys
      | FStarC_Extraction_ML_Syntax.MLM_Top uu___ ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStarC_Extraction_ML_Syntax.MLM_Exn (m, uu___) ->
          (FStarC_Compiler_Util.print1_warning
             "Not extracting exception %s to KaRaMeL (exceptions unsupported)\n"
             m;
           [])
let (translate_module :
  FStarC_Extraction_ML_UEnv.uenv ->
    (FStarC_Extraction_ML_Syntax.mlpath * (FStarC_Extraction_ML_Syntax.mlsig
      * FStarC_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option
      * FStarC_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uenv ->
    fun m ->
      let uu___ = m in
      match uu___ with
      | (module_name, modul, uu___1) ->
          let module_name1 =
            FStarC_Compiler_List.op_At
              (FStar_Pervasives_Native.fst module_name)
              [FStar_Pervasives_Native.snd module_name] in
          let program1 =
            match modul with
            | FStar_Pervasives_Native.Some (_signature, decls) ->
                FStarC_Compiler_List.collect
                  (translate_decl (empty uenv module_name1)) decls
            | uu___2 ->
                failwith "Unexpected standalone interface or nested modules" in
          ((FStarC_Compiler_String.concat "_" module_name1), program1)
let (translate :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Extraction_ML_Syntax.mllib -> file Prims.list)
  =
  fun ue ->
    fun uu___ ->
      match uu___ with
      | FStarC_Extraction_ML_Syntax.MLLib modules ->
          FStarC_Compiler_List.filter_map
            (fun m ->
               let m_name =
                 let uu___1 = m in
                 match uu___1 with
                 | (path, uu___2, uu___3) ->
                     FStarC_Extraction_ML_Syntax.string_of_mlpath path in
               try
                 (fun uu___1 ->
                    match () with
                    | () ->
                        ((let uu___3 =
                            let uu___4 = FStarC_Options.silent () in
                            Prims.op_Negation uu___4 in
                          if uu___3
                          then
                            FStarC_Compiler_Util.print1
                              "Attempting to translate module %s\n" m_name
                          else ());
                         (let uu___3 = translate_module ue m in
                          FStar_Pervasives_Native.Some uu___3))) ()
               with
               | uu___1 ->
                   ((let uu___3 = FStarC_Compiler_Util.print_exn uu___1 in
                     FStarC_Compiler_Util.print2
                       "Unable to translate module: %s because:\n  %s\n"
                       m_name uu___3);
                    FStar_Pervasives_Native.None)) modules
let (uu___0 : unit) =
  register_post_translate_type_without_decay translate_type_without_decay';
  register_post_translate_type translate_type';
  register_post_translate_type_decl translate_type_decl';
  register_post_translate_expr translate_expr'