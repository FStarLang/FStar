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
  | ESizeof of typ 
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
  | Float32 
  | Float64 
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
let uu___is_DGlobal (projectee : decl) : Prims.bool=
  match projectee with | DGlobal _0 -> true | uu___ -> false
let __proj__DGlobal__item___0 (projectee : decl) :
  (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
    typ * expr)=
  match projectee with | DGlobal _0 -> _0
let uu___is_DFunction (projectee : decl) : Prims.bool=
  match projectee with | DFunction _0 -> true | uu___ -> false
let __proj__DFunction__item___0 (projectee : decl) :
  (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
    (Prims.string Prims.list * Prims.string) * binder Prims.list * expr)=
  match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias (projectee : decl) : Prims.bool=
  match projectee with | DTypeAlias _0 -> true | uu___ -> false
let __proj__DTypeAlias__item___0 (projectee : decl) :
  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
    typ)=
  match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat (projectee : decl) : Prims.bool=
  match projectee with | DTypeFlat _0 -> true | uu___ -> false
let __proj__DTypeFlat__item___0 (projectee : decl) :
  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
    (Prims.string * (typ * Prims.bool)) Prims.list)=
  match projectee with | DTypeFlat _0 -> _0
let uu___is_DUnusedRetainedForBackwardsCompat (projectee : decl) :
  Prims.bool=
  match projectee with
  | DUnusedRetainedForBackwardsCompat _0 -> true
  | uu___ -> false
let __proj__DUnusedRetainedForBackwardsCompat__item___0 (projectee : decl) :
  (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
    Prims.list * Prims.string) * typ)=
  match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
let uu___is_DTypeVariant (projectee : decl) : Prims.bool=
  match projectee with | DTypeVariant _0 -> true | uu___ -> false
let __proj__DTypeVariant__item___0 (projectee : decl) :
  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
    (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list)
    Prims.list)=
  match projectee with | DTypeVariant _0 -> _0
let uu___is_DTypeAbstractStruct (projectee : decl) : Prims.bool=
  match projectee with | DTypeAbstractStruct _0 -> true | uu___ -> false
let __proj__DTypeAbstractStruct__item___0 (projectee : decl) :
  (Prims.string Prims.list * Prims.string)=
  match projectee with | DTypeAbstractStruct _0 -> _0
let uu___is_DExternal (projectee : decl) : Prims.bool=
  match projectee with | DExternal _0 -> true | uu___ -> false
let __proj__DExternal__item___0 (projectee : decl) :
  (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
    Prims.list * Prims.string) * typ * Prims.string Prims.list)=
  match projectee with | DExternal _0 -> _0
let uu___is_DUntaggedUnion (projectee : decl) : Prims.bool=
  match projectee with | DUntaggedUnion _0 -> true | uu___ -> false
let __proj__DUntaggedUnion__item___0 (projectee : decl) :
  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
    (Prims.string * typ) Prims.list)=
  match projectee with | DUntaggedUnion _0 -> _0
let uu___is_StdCall (projectee : cc) : Prims.bool=
  match projectee with | StdCall -> true | uu___ -> false
let uu___is_CDecl (projectee : cc) : Prims.bool=
  match projectee with | CDecl -> true | uu___ -> false
let uu___is_FastCall (projectee : cc) : Prims.bool=
  match projectee with | FastCall -> true | uu___ -> false
let uu___is_Private (projectee : flag) : Prims.bool=
  match projectee with | Private -> true | uu___ -> false
let uu___is_WipeBody (projectee : flag) : Prims.bool=
  match projectee with | WipeBody -> true | uu___ -> false
let uu___is_CInline (projectee : flag) : Prims.bool=
  match projectee with | CInline -> true | uu___ -> false
let uu___is_Substitute (projectee : flag) : Prims.bool=
  match projectee with | Substitute -> true | uu___ -> false
let uu___is_GCType (projectee : flag) : Prims.bool=
  match projectee with | GCType -> true | uu___ -> false
let uu___is_Comment (projectee : flag) : Prims.bool=
  match projectee with | Comment _0 -> true | uu___ -> false
let __proj__Comment__item___0 (projectee : flag) : Prims.string=
  match projectee with | Comment _0 -> _0
let uu___is_MustDisappear (projectee : flag) : Prims.bool=
  match projectee with | MustDisappear -> true | uu___ -> false
let uu___is_Const (projectee : flag) : Prims.bool=
  match projectee with | Const _0 -> true | uu___ -> false
let __proj__Const__item___0 (projectee : flag) : Prims.string=
  match projectee with | Const _0 -> _0
let uu___is_Prologue (projectee : flag) : Prims.bool=
  match projectee with | Prologue _0 -> true | uu___ -> false
let __proj__Prologue__item___0 (projectee : flag) : Prims.string=
  match projectee with | Prologue _0 -> _0
let uu___is_Epilogue (projectee : flag) : Prims.bool=
  match projectee with | Epilogue _0 -> true | uu___ -> false
let __proj__Epilogue__item___0 (projectee : flag) : Prims.string=
  match projectee with | Epilogue _0 -> _0
let uu___is_Abstract (projectee : flag) : Prims.bool=
  match projectee with | Abstract -> true | uu___ -> false
let uu___is_IfDef (projectee : flag) : Prims.bool=
  match projectee with | IfDef -> true | uu___ -> false
let uu___is_Macro (projectee : flag) : Prims.bool=
  match projectee with | Macro -> true | uu___ -> false
let uu___is_Deprecated (projectee : flag) : Prims.bool=
  match projectee with | Deprecated _0 -> true | uu___ -> false
let __proj__Deprecated__item___0 (projectee : flag) : Prims.string=
  match projectee with | Deprecated _0 -> _0
let uu___is_CNoInline (projectee : flag) : Prims.bool=
  match projectee with | CNoInline -> true | uu___ -> false
let uu___is_Eternal (projectee : lifetime) : Prims.bool=
  match projectee with | Eternal -> true | uu___ -> false
let uu___is_Stack (projectee : lifetime) : Prims.bool=
  match projectee with | Stack -> true | uu___ -> false
let uu___is_ManuallyManaged (projectee : lifetime) : Prims.bool=
  match projectee with | ManuallyManaged -> true | uu___ -> false
let uu___is_EBound (projectee : expr) : Prims.bool=
  match projectee with | EBound _0 -> true | uu___ -> false
let __proj__EBound__item___0 (projectee : expr) : Prims.int=
  match projectee with | EBound _0 -> _0
let uu___is_EQualified (projectee : expr) : Prims.bool=
  match projectee with | EQualified _0 -> true | uu___ -> false
let __proj__EQualified__item___0 (projectee : expr) :
  (Prims.string Prims.list * Prims.string)=
  match projectee with | EQualified _0 -> _0
let uu___is_EConstant (projectee : expr) : Prims.bool=
  match projectee with | EConstant _0 -> true | uu___ -> false
let __proj__EConstant__item___0 (projectee : expr) : (width * Prims.string)=
  match projectee with | EConstant _0 -> _0
let uu___is_EUnit (projectee : expr) : Prims.bool=
  match projectee with | EUnit -> true | uu___ -> false
let uu___is_EApp (projectee : expr) : Prims.bool=
  match projectee with | EApp _0 -> true | uu___ -> false
let __proj__EApp__item___0 (projectee : expr) : (expr * expr Prims.list)=
  match projectee with | EApp _0 -> _0
let uu___is_ETypApp (projectee : expr) : Prims.bool=
  match projectee with | ETypApp _0 -> true | uu___ -> false
let __proj__ETypApp__item___0 (projectee : expr) : (expr * typ Prims.list)=
  match projectee with | ETypApp _0 -> _0
let uu___is_ELet (projectee : expr) : Prims.bool=
  match projectee with | ELet _0 -> true | uu___ -> false
let __proj__ELet__item___0 (projectee : expr) : (binder * expr * expr)=
  match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse (projectee : expr) : Prims.bool=
  match projectee with | EIfThenElse _0 -> true | uu___ -> false
let __proj__EIfThenElse__item___0 (projectee : expr) : (expr * expr * expr)=
  match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence (projectee : expr) : Prims.bool=
  match projectee with | ESequence _0 -> true | uu___ -> false
let __proj__ESequence__item___0 (projectee : expr) : expr Prims.list=
  match projectee with | ESequence _0 -> _0
let uu___is_EAssign (projectee : expr) : Prims.bool=
  match projectee with | EAssign _0 -> true | uu___ -> false
let __proj__EAssign__item___0 (projectee : expr) : (expr * expr)=
  match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate (projectee : expr) : Prims.bool=
  match projectee with | EBufCreate _0 -> true | uu___ -> false
let __proj__EBufCreate__item___0 (projectee : expr) :
  (lifetime * expr * expr)= match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead (projectee : expr) : Prims.bool=
  match projectee with | EBufRead _0 -> true | uu___ -> false
let __proj__EBufRead__item___0 (projectee : expr) : (expr * expr)=
  match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite (projectee : expr) : Prims.bool=
  match projectee with | EBufWrite _0 -> true | uu___ -> false
let __proj__EBufWrite__item___0 (projectee : expr) : (expr * expr * expr)=
  match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub (projectee : expr) : Prims.bool=
  match projectee with | EBufSub _0 -> true | uu___ -> false
let __proj__EBufSub__item___0 (projectee : expr) : (expr * expr)=
  match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit (projectee : expr) : Prims.bool=
  match projectee with | EBufBlit _0 -> true | uu___ -> false
let __proj__EBufBlit__item___0 (projectee : expr) :
  (expr * expr * expr * expr * expr)=
  match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch (projectee : expr) : Prims.bool=
  match projectee with | EMatch _0 -> true | uu___ -> false
let __proj__EMatch__item___0 (projectee : expr) :
  (expr * (pattern * expr) Prims.list)=
  match projectee with | EMatch _0 -> _0
let uu___is_EOp (projectee : expr) : Prims.bool=
  match projectee with | EOp _0 -> true | uu___ -> false
let __proj__EOp__item___0 (projectee : expr) : (op * width)=
  match projectee with | EOp _0 -> _0
let uu___is_ECast (projectee : expr) : Prims.bool=
  match projectee with | ECast _0 -> true | uu___ -> false
let __proj__ECast__item___0 (projectee : expr) : (expr * typ)=
  match projectee with | ECast _0 -> _0
let uu___is_EPushFrame (projectee : expr) : Prims.bool=
  match projectee with | EPushFrame -> true | uu___ -> false
let uu___is_EPopFrame (projectee : expr) : Prims.bool=
  match projectee with | EPopFrame -> true | uu___ -> false
let uu___is_EBool (projectee : expr) : Prims.bool=
  match projectee with | EBool _0 -> true | uu___ -> false
let __proj__EBool__item___0 (projectee : expr) : Prims.bool=
  match projectee with | EBool _0 -> _0
let uu___is_EAny (projectee : expr) : Prims.bool=
  match projectee with | EAny -> true | uu___ -> false
let uu___is_EAbort (projectee : expr) : Prims.bool=
  match projectee with | EAbort -> true | uu___ -> false
let uu___is_EReturn (projectee : expr) : Prims.bool=
  match projectee with | EReturn _0 -> true | uu___ -> false
let __proj__EReturn__item___0 (projectee : expr) : expr=
  match projectee with | EReturn _0 -> _0
let uu___is_EFlat (projectee : expr) : Prims.bool=
  match projectee with | EFlat _0 -> true | uu___ -> false
let __proj__EFlat__item___0 (projectee : expr) :
  (typ * (Prims.string * expr) Prims.list)=
  match projectee with | EFlat _0 -> _0
let uu___is_EField (projectee : expr) : Prims.bool=
  match projectee with | EField _0 -> true | uu___ -> false
let __proj__EField__item___0 (projectee : expr) :
  (typ * expr * Prims.string)= match projectee with | EField _0 -> _0
let uu___is_EWhile (projectee : expr) : Prims.bool=
  match projectee with | EWhile _0 -> true | uu___ -> false
let __proj__EWhile__item___0 (projectee : expr) : (expr * expr)=
  match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL (projectee : expr) : Prims.bool=
  match projectee with | EBufCreateL _0 -> true | uu___ -> false
let __proj__EBufCreateL__item___0 (projectee : expr) :
  (lifetime * expr Prims.list)= match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple (projectee : expr) : Prims.bool=
  match projectee with | ETuple _0 -> true | uu___ -> false
let __proj__ETuple__item___0 (projectee : expr) : expr Prims.list=
  match projectee with | ETuple _0 -> _0
let uu___is_ECons (projectee : expr) : Prims.bool=
  match projectee with | ECons _0 -> true | uu___ -> false
let __proj__ECons__item___0 (projectee : expr) :
  (typ * Prims.string * expr Prims.list)=
  match projectee with | ECons _0 -> _0
let uu___is_EBufFill (projectee : expr) : Prims.bool=
  match projectee with | EBufFill _0 -> true | uu___ -> false
let __proj__EBufFill__item___0 (projectee : expr) : (expr * expr * expr)=
  match projectee with | EBufFill _0 -> _0
let uu___is_EString (projectee : expr) : Prims.bool=
  match projectee with | EString _0 -> true | uu___ -> false
let __proj__EString__item___0 (projectee : expr) : Prims.string=
  match projectee with | EString _0 -> _0
let uu___is_EFun (projectee : expr) : Prims.bool=
  match projectee with | EFun _0 -> true | uu___ -> false
let __proj__EFun__item___0 (projectee : expr) :
  (binder Prims.list * expr * typ)= match projectee with | EFun _0 -> _0
let uu___is_EAbortS (projectee : expr) : Prims.bool=
  match projectee with | EAbortS _0 -> true | uu___ -> false
let __proj__EAbortS__item___0 (projectee : expr) : Prims.string=
  match projectee with | EAbortS _0 -> _0
let uu___is_EBufFree (projectee : expr) : Prims.bool=
  match projectee with | EBufFree _0 -> true | uu___ -> false
let __proj__EBufFree__item___0 (projectee : expr) : expr=
  match projectee with | EBufFree _0 -> _0
let uu___is_EBufCreateNoInit (projectee : expr) : Prims.bool=
  match projectee with | EBufCreateNoInit _0 -> true | uu___ -> false
let __proj__EBufCreateNoInit__item___0 (projectee : expr) :
  (lifetime * expr)= match projectee with | EBufCreateNoInit _0 -> _0
let uu___is_EAbortT (projectee : expr) : Prims.bool=
  match projectee with | EAbortT _0 -> true | uu___ -> false
let __proj__EAbortT__item___0 (projectee : expr) : (Prims.string * typ)=
  match projectee with | EAbortT _0 -> _0
let uu___is_EComment (projectee : expr) : Prims.bool=
  match projectee with | EComment _0 -> true | uu___ -> false
let __proj__EComment__item___0 (projectee : expr) :
  (Prims.string * expr * Prims.string)=
  match projectee with | EComment _0 -> _0
let uu___is_EStandaloneComment (projectee : expr) : Prims.bool=
  match projectee with | EStandaloneComment _0 -> true | uu___ -> false
let __proj__EStandaloneComment__item___0 (projectee : expr) : Prims.string=
  match projectee with | EStandaloneComment _0 -> _0
let uu___is_EAddrOf (projectee : expr) : Prims.bool=
  match projectee with | EAddrOf _0 -> true | uu___ -> false
let __proj__EAddrOf__item___0 (projectee : expr) : expr=
  match projectee with | EAddrOf _0 -> _0
let uu___is_EBufNull (projectee : expr) : Prims.bool=
  match projectee with | EBufNull _0 -> true | uu___ -> false
let __proj__EBufNull__item___0 (projectee : expr) : typ=
  match projectee with | EBufNull _0 -> _0
let uu___is_EBufDiff (projectee : expr) : Prims.bool=
  match projectee with | EBufDiff _0 -> true | uu___ -> false
let __proj__EBufDiff__item___0 (projectee : expr) : (expr * expr)=
  match projectee with | EBufDiff _0 -> _0
let uu___is_ESizeof (projectee : expr) : Prims.bool=
  match projectee with | ESizeof _0 -> true | uu___ -> false
let __proj__ESizeof__item___0 (projectee : expr) : typ=
  match projectee with | ESizeof _0 -> _0
let uu___is_Add (projectee : op) : Prims.bool=
  match projectee with | Add -> true | uu___ -> false
let uu___is_AddW (projectee : op) : Prims.bool=
  match projectee with | AddW -> true | uu___ -> false
let uu___is_Sub (projectee : op) : Prims.bool=
  match projectee with | Sub -> true | uu___ -> false
let uu___is_SubW (projectee : op) : Prims.bool=
  match projectee with | SubW -> true | uu___ -> false
let uu___is_Div (projectee : op) : Prims.bool=
  match projectee with | Div -> true | uu___ -> false
let uu___is_DivW (projectee : op) : Prims.bool=
  match projectee with | DivW -> true | uu___ -> false
let uu___is_Mult (projectee : op) : Prims.bool=
  match projectee with | Mult -> true | uu___ -> false
let uu___is_MultW (projectee : op) : Prims.bool=
  match projectee with | MultW -> true | uu___ -> false
let uu___is_Mod (projectee : op) : Prims.bool=
  match projectee with | Mod -> true | uu___ -> false
let uu___is_BOr (projectee : op) : Prims.bool=
  match projectee with | BOr -> true | uu___ -> false
let uu___is_BAnd (projectee : op) : Prims.bool=
  match projectee with | BAnd -> true | uu___ -> false
let uu___is_BXor (projectee : op) : Prims.bool=
  match projectee with | BXor -> true | uu___ -> false
let uu___is_BShiftL (projectee : op) : Prims.bool=
  match projectee with | BShiftL -> true | uu___ -> false
let uu___is_BShiftR (projectee : op) : Prims.bool=
  match projectee with | BShiftR -> true | uu___ -> false
let uu___is_BNot (projectee : op) : Prims.bool=
  match projectee with | BNot -> true | uu___ -> false
let uu___is_Eq (projectee : op) : Prims.bool=
  match projectee with | Eq -> true | uu___ -> false
let uu___is_Neq (projectee : op) : Prims.bool=
  match projectee with | Neq -> true | uu___ -> false
let uu___is_Lt (projectee : op) : Prims.bool=
  match projectee with | Lt -> true | uu___ -> false
let uu___is_Lte (projectee : op) : Prims.bool=
  match projectee with | Lte -> true | uu___ -> false
let uu___is_Gt (projectee : op) : Prims.bool=
  match projectee with | Gt -> true | uu___ -> false
let uu___is_Gte (projectee : op) : Prims.bool=
  match projectee with | Gte -> true | uu___ -> false
let uu___is_And (projectee : op) : Prims.bool=
  match projectee with | And -> true | uu___ -> false
let uu___is_Or (projectee : op) : Prims.bool=
  match projectee with | Or -> true | uu___ -> false
let uu___is_Xor (projectee : op) : Prims.bool=
  match projectee with | Xor -> true | uu___ -> false
let uu___is_Not (projectee : op) : Prims.bool=
  match projectee with | Not -> true | uu___ -> false
let uu___is_PUnit (projectee : pattern) : Prims.bool=
  match projectee with | PUnit -> true | uu___ -> false
let uu___is_PBool (projectee : pattern) : Prims.bool=
  match projectee with | PBool _0 -> true | uu___ -> false
let __proj__PBool__item___0 (projectee : pattern) : Prims.bool=
  match projectee with | PBool _0 -> _0
let uu___is_PVar (projectee : pattern) : Prims.bool=
  match projectee with | PVar _0 -> true | uu___ -> false
let __proj__PVar__item___0 (projectee : pattern) : binder=
  match projectee with | PVar _0 -> _0
let uu___is_PCons (projectee : pattern) : Prims.bool=
  match projectee with | PCons _0 -> true | uu___ -> false
let __proj__PCons__item___0 (projectee : pattern) :
  (Prims.string * pattern Prims.list)= match projectee with | PCons _0 -> _0
let uu___is_PTuple (projectee : pattern) : Prims.bool=
  match projectee with | PTuple _0 -> true | uu___ -> false
let __proj__PTuple__item___0 (projectee : pattern) : pattern Prims.list=
  match projectee with | PTuple _0 -> _0
let uu___is_PRecord (projectee : pattern) : Prims.bool=
  match projectee with | PRecord _0 -> true | uu___ -> false
let __proj__PRecord__item___0 (projectee : pattern) :
  (Prims.string * pattern) Prims.list=
  match projectee with | PRecord _0 -> _0
let uu___is_PConstant (projectee : pattern) : Prims.bool=
  match projectee with | PConstant _0 -> true | uu___ -> false
let __proj__PConstant__item___0 (projectee : pattern) :
  (width * Prims.string)= match projectee with | PConstant _0 -> _0
let uu___is_UInt8 (projectee : width) : Prims.bool=
  match projectee with | UInt8 -> true | uu___ -> false
let uu___is_UInt16 (projectee : width) : Prims.bool=
  match projectee with | UInt16 -> true | uu___ -> false
let uu___is_UInt32 (projectee : width) : Prims.bool=
  match projectee with | UInt32 -> true | uu___ -> false
let uu___is_UInt64 (projectee : width) : Prims.bool=
  match projectee with | UInt64 -> true | uu___ -> false
let uu___is_Int8 (projectee : width) : Prims.bool=
  match projectee with | Int8 -> true | uu___ -> false
let uu___is_Int16 (projectee : width) : Prims.bool=
  match projectee with | Int16 -> true | uu___ -> false
let uu___is_Int32 (projectee : width) : Prims.bool=
  match projectee with | Int32 -> true | uu___ -> false
let uu___is_Int64 (projectee : width) : Prims.bool=
  match projectee with | Int64 -> true | uu___ -> false
let uu___is_Bool (projectee : width) : Prims.bool=
  match projectee with | Bool -> true | uu___ -> false
let uu___is_CInt (projectee : width) : Prims.bool=
  match projectee with | CInt -> true | uu___ -> false
let uu___is_SizeT (projectee : width) : Prims.bool=
  match projectee with | SizeT -> true | uu___ -> false
let uu___is_PtrdiffT (projectee : width) : Prims.bool=
  match projectee with | PtrdiffT -> true | uu___ -> false
let uu___is_Float32 (projectee : width) : Prims.bool=
  match projectee with | Float32 -> true | uu___ -> false
let uu___is_Float64 (projectee : width) : Prims.bool=
  match projectee with | Float64 -> true | uu___ -> false
let __proj__Mkbinder__item__name (projectee : binder) : Prims.string=
  match projectee with | { name; typ = typ1; mut; meta;_} -> name
let __proj__Mkbinder__item__typ (projectee : binder) : typ=
  match projectee with | { name; typ = typ1; mut; meta;_} -> typ1
let __proj__Mkbinder__item__mut (projectee : binder) : Prims.bool=
  match projectee with | { name; typ = typ1; mut; meta;_} -> mut
let __proj__Mkbinder__item__meta (projectee : binder) : flag Prims.list=
  match projectee with | { name; typ = typ1; mut; meta;_} -> meta
let uu___is_TInt (projectee : typ) : Prims.bool=
  match projectee with | TInt _0 -> true | uu___ -> false
let __proj__TInt__item___0 (projectee : typ) : width=
  match projectee with | TInt _0 -> _0
let uu___is_TBuf (projectee : typ) : Prims.bool=
  match projectee with | TBuf _0 -> true | uu___ -> false
let __proj__TBuf__item___0 (projectee : typ) : typ=
  match projectee with | TBuf _0 -> _0
let uu___is_TUnit (projectee : typ) : Prims.bool=
  match projectee with | TUnit -> true | uu___ -> false
let uu___is_TQualified (projectee : typ) : Prims.bool=
  match projectee with | TQualified _0 -> true | uu___ -> false
let __proj__TQualified__item___0 (projectee : typ) :
  (Prims.string Prims.list * Prims.string)=
  match projectee with | TQualified _0 -> _0
let uu___is_TBool (projectee : typ) : Prims.bool=
  match projectee with | TBool -> true | uu___ -> false
let uu___is_TAny (projectee : typ) : Prims.bool=
  match projectee with | TAny -> true | uu___ -> false
let uu___is_TArrow (projectee : typ) : Prims.bool=
  match projectee with | TArrow _0 -> true | uu___ -> false
let __proj__TArrow__item___0 (projectee : typ) : (typ * typ)=
  match projectee with | TArrow _0 -> _0
let uu___is_TBound (projectee : typ) : Prims.bool=
  match projectee with | TBound _0 -> true | uu___ -> false
let __proj__TBound__item___0 (projectee : typ) : Prims.int=
  match projectee with | TBound _0 -> _0
let uu___is_TApp (projectee : typ) : Prims.bool=
  match projectee with | TApp _0 -> true | uu___ -> false
let __proj__TApp__item___0 (projectee : typ) :
  ((Prims.string Prims.list * Prims.string) * typ Prims.list)=
  match projectee with | TApp _0 -> _0
let uu___is_TTuple (projectee : typ) : Prims.bool=
  match projectee with | TTuple _0 -> true | uu___ -> false
let __proj__TTuple__item___0 (projectee : typ) : typ Prims.list=
  match projectee with | TTuple _0 -> _0
let uu___is_TConstBuf (projectee : typ) : Prims.bool=
  match projectee with | TConstBuf _0 -> true | uu___ -> false
let __proj__TConstBuf__item___0 (projectee : typ) : typ=
  match projectee with | TConstBuf _0 -> _0
let uu___is_TArray (projectee : typ) : Prims.bool=
  match projectee with | TArray _0 -> true | uu___ -> false
let __proj__TArray__item___0 (projectee : typ) :
  (typ * (width * Prims.string))= match projectee with | TArray _0 -> _0
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
let pretty_width : width FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | UInt8 -> FStar_Pprint.doc_of_string "UInt8"
         | UInt16 -> FStar_Pprint.doc_of_string "UInt16"
         | UInt32 -> FStar_Pprint.doc_of_string "UInt32"
         | UInt64 -> FStar_Pprint.doc_of_string "UInt64"
         | Int8 -> FStar_Pprint.doc_of_string "Int8"
         | Int16 -> FStar_Pprint.doc_of_string "Int16"
         | Int32 -> FStar_Pprint.doc_of_string "Int32"
         | Int64 -> FStar_Pprint.doc_of_string "Int64"
         | Bool -> FStar_Pprint.doc_of_string "Bool"
         | CInt -> FStar_Pprint.doc_of_string "CInt"
         | SizeT -> FStar_Pprint.doc_of_string "SizeT"
         | PtrdiffT -> FStar_Pprint.doc_of_string "PtrdiffT"
         | Float32 -> FStar_Pprint.doc_of_string "Float32"
         | Float64 -> FStar_Pprint.doc_of_string "Float64")
  }
let showable_width : width FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_width
let ctor (n : Prims.string) (args : FStar_Pprint.document Prims.list) :
  FStar_Pprint.document=
  FStar_Pprint.nest (Prims.of_int 2)
    (FStar_Pprint.group
       (FStar_Pprint.parens
          (FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
             ((FStar_Pprint.doc_of_string n) :: args))))
let pp_list' (f : 'a -> FStar_Pprint.document) (xs : 'a Prims.list) :
  FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Pprint.flow_map
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
             (FStar_Pprint.break_ Prims.int_one)) f xs in
      FStar_Pprint.brackets uu___2 in
    FStar_Pprint.nest (Prims.of_int 2) uu___1 in
  FStar_Pprint.group uu___
let rec typ_to_doc (t : typ) : FStar_Pprint.document=
  match t with
  | TInt w ->
      let uu___ = let uu___1 = FStarC_Class_PP.pp pretty_width w in [uu___1] in
      ctor "TInt" uu___
  | TBuf t1 ->
      let uu___ = let uu___1 = typ_to_doc t1 in [uu___1] in ctor "TBuf" uu___
  | TUnit -> FStar_Pprint.doc_of_string "TUnit"
  | TQualified x ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_tuple2
                 (FStarC_Class_Show.show_list
                    FStarC_Class_Show.showable_string)
                 FStarC_Class_Show.showable_string) x in
          FStar_Pprint.doc_of_string uu___2 in
        [uu___1] in
      ctor "TQualified" uu___
  | TBool -> FStar_Pprint.doc_of_string "TBool"
  | TAny -> FStar_Pprint.doc_of_string "TAny"
  | TArrow (t1, t2) ->
      let uu___ =
        let uu___1 = typ_to_doc t1 in
        let uu___2 = let uu___3 = typ_to_doc t2 in [uu___3] in uu___1 ::
          uu___2 in
      ctor "TArrow" uu___
  | TBound x ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int x in [uu___1] in
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
          FStar_Pprint.doc_of_string uu___2 in
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
                [uu___6;
                FStar_Pprint.doc_of_string (FStar_Pervasives_Native.snd c)] in
              FStar_Pprint.separate FStar_Pprint.comma uu___5 in
            FStar_Pprint.parens uu___4 in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "TArray" uu___
let pretty_typ : typ FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = typ_to_doc }
let showable_typ : typ FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_typ
let pretty_string : Prims.string FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun s -> FStar_Pprint.dquotes (FStar_Pprint.doc_of_string s))
  }
let pretty_flag : flag FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | Private -> FStar_Pprint.doc_of_string "Private"
         | WipeBody -> FStar_Pprint.doc_of_string "WipeBody"
         | CInline -> FStar_Pprint.doc_of_string "CInline"
         | Substitute -> FStar_Pprint.doc_of_string "Substitute"
         | GCType -> FStar_Pprint.doc_of_string "GCType"
         | Comment s ->
             let uu___1 =
               let uu___2 = FStarC_Class_PP.pp pretty_string s in [uu___2] in
             ctor "Comment" uu___1
         | MustDisappear -> FStar_Pprint.doc_of_string "MustDisappear"
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
         | Abstract -> FStar_Pprint.doc_of_string "Abstract"
         | IfDef -> FStar_Pprint.doc_of_string "IfDef"
         | Macro -> FStar_Pprint.doc_of_string "Macro"
         | Deprecated s ->
             let uu___1 =
               let uu___2 = FStarC_Class_PP.pp pretty_string s in [uu___2] in
             ctor "Deprecated" uu___1
         | CNoInline -> FStar_Pprint.doc_of_string "CNoInline")
  }
let spaced (a : FStar_Pprint.document) : FStar_Pprint.document=
  FStar_Pprint.op_Hat_Hat (FStar_Pprint.break_ Prims.int_one)
    (FStar_Pprint.op_Hat_Hat a (FStar_Pprint.break_ Prims.int_one))
let record (fs : FStar_Pprint.document Prims.list) : FStar_Pprint.document=
  FStar_Pprint.group
    (FStar_Pprint.nest (Prims.of_int 2)
       (FStar_Pprint.braces
          (spaced
             (FStar_Pprint.separate
                (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                   (FStar_Pprint.break_ Prims.int_one)) fs))))
let fld (n : Prims.string) (v : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.group
    (FStar_Pprint.nest (Prims.of_int 2)
       (FStar_Pprint.op_Hat_Slash_Hat
          (FStar_Pprint.doc_of_string (Prims.strcat n " =")) v))
let pretty_binder : binder FStarC_Class_PP.pretty=
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
let showable_binder : binder FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_binder
let pretty_lifetime : lifetime FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | Eternal -> FStar_Pprint.doc_of_string "Eternal"
         | Stack -> FStar_Pprint.doc_of_string "Stack"
         | ManuallyManaged -> FStar_Pprint.doc_of_string "ManuallyManaged")
  }
let showable_lifetime : lifetime FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_lifetime
let pretty_op : op FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | Add -> FStar_Pprint.doc_of_string "Add"
         | AddW -> FStar_Pprint.doc_of_string "AddW"
         | Sub -> FStar_Pprint.doc_of_string "Sub"
         | SubW -> FStar_Pprint.doc_of_string "SubW"
         | Div -> FStar_Pprint.doc_of_string "Div"
         | DivW -> FStar_Pprint.doc_of_string "DivW"
         | Mult -> FStar_Pprint.doc_of_string "Mult"
         | MultW -> FStar_Pprint.doc_of_string "MultW"
         | Mod -> FStar_Pprint.doc_of_string "Mod"
         | BOr -> FStar_Pprint.doc_of_string "BOr"
         | BAnd -> FStar_Pprint.doc_of_string "BAnd"
         | BXor -> FStar_Pprint.doc_of_string "BXor"
         | BShiftL -> FStar_Pprint.doc_of_string "BShiftL"
         | BShiftR -> FStar_Pprint.doc_of_string "BShiftR"
         | BNot -> FStar_Pprint.doc_of_string "BNot"
         | Eq -> FStar_Pprint.doc_of_string "Eq"
         | Neq -> FStar_Pprint.doc_of_string "Neq"
         | Lt -> FStar_Pprint.doc_of_string "Lt"
         | Lte -> FStar_Pprint.doc_of_string "Lte"
         | Gt -> FStar_Pprint.doc_of_string "Gt"
         | Gte -> FStar_Pprint.doc_of_string "Gte"
         | And -> FStar_Pprint.doc_of_string "And"
         | Or -> FStar_Pprint.doc_of_string "Or"
         | Xor -> FStar_Pprint.doc_of_string "Xor"
         | Not -> FStar_Pprint.doc_of_string "Not")
  }
let showable_op : op FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_op
let pretty_cc : cc FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | StdCall -> FStar_Pprint.doc_of_string "StdCall"
         | CDecl -> FStar_Pprint.doc_of_string "CDecl"
         | FastCall -> FStar_Pprint.doc_of_string "FastCall")
  }
let showable_cc : cc FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_cc
let rec pattern_to_doc (p : pattern) : FStar_Pprint.document=
  match p with
  | PUnit -> FStar_Pprint.doc_of_string "PUnit"
  | PBool b ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool b in [uu___1] in
      ctor "PBool" uu___
  | PVar b ->
      let uu___ = let uu___1 = FStarC_Class_PP.pp pretty_binder b in [uu___1] in
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
            FStarC_List.map
              (fun uu___3 ->
                 match uu___3 with
                 | (s, p1) -> let uu___4 = pattern_to_doc p1 in fld s uu___4)
              fs in
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
let pretty_pattern : pattern FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pattern_to_doc }
let showable_pattern : pattern FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_pattern
let rec decl_to_doc (d : decl) : FStar_Pprint.document=
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
                       (FStarC_Class_PP.pp_list pretty_string) pretty_string)
                    x in
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
                  FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_string)
                    xs in
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
                     (FStarC_Class_PP.pp_tuple2 pretty_string pretty_typ)) xs in
              [uu___7] in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "DUntaggedUnion" uu___
and expr_to_doc (e : expr) : FStar_Pprint.document=
  match e with
  | EBound x ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int x in [uu___1] in
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
  | EUnit -> FStar_Pprint.doc_of_string "EUnit"
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
        let uu___2 = let uu___3 = pp_list' pp_branch bs in [uu___3] in uu___1
          :: uu___2 in
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
        let uu___2 = let uu___3 = FStarC_Class_PP.pp pretty_typ y in [uu___3] in
        uu___1 :: uu___2 in
      ctor "ECast" uu___
  | EPushFrame -> FStar_Pprint.doc_of_string "EPushFrame"
  | EPopFrame -> FStar_Pprint.doc_of_string "EPopFrame"
  | EBool x ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool x in [uu___1] in
      ctor "EBool" uu___
  | EAny -> FStar_Pprint.doc_of_string "EAny"
  | EAbort -> FStar_Pprint.doc_of_string "EAbort"
  | EReturn x ->
      let uu___ = let uu___1 = expr_to_doc x in [uu___1] in
      ctor "EReturn" uu___
  | EFlat (x, xs) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp pretty_typ x in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_List.map
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
      let uu___ = let uu___1 = FStarC_Class_PP.pp pretty_string x in [uu___1] in
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
      let uu___ = let uu___1 = FStarC_Class_PP.pp pretty_string x in [uu___1] in
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
        let uu___2 = let uu___3 = FStarC_Class_PP.pp pretty_typ y in [uu___3] in
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
      let uu___ = let uu___1 = FStarC_Class_PP.pp pretty_string x in [uu___1] in
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
  | ESizeof t ->
      let uu___ = let uu___1 = FStarC_Class_PP.pp pretty_typ t in [uu___1] in
      ctor "ESizeof" uu___
and pp_branch (b : branch) : FStar_Pprint.document=
  let uu___ = b in
  match uu___ with
  | (p, e) ->
      let uu___1 =
        let uu___2 = FStarC_Class_PP.pp pretty_pattern p in
        let uu___3 =
          let uu___4 = expr_to_doc e in
          FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.comma uu___4 in
        FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
      FStar_Pprint.parens uu___1
let pretty_expr : expr FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = expr_to_doc }
let pretty_decl : decl FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = decl_to_doc }
let pretty_branch : branch FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pp_branch }
let showable_expr : expr FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_expr
let showable_decl : decl FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_decl
let showable_branch : branch FStarC_Class_Show.showable=
  FStarC_Class_PP.showable_from_pretty pretty_branch
