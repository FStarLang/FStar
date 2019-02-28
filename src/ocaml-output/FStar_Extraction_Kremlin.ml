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
    match projectee with | DGlobal _0 -> true | uu____46584 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____46696 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____46822 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____46930 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____47063 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____47181 -> false
  
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
    | uu____47323 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____47366 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____47377 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____47388 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____47399 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____47410 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____47421 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____47432 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____47443 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____47456 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____47478 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____47491 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____47515 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____47539 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____47561 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____47572 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____47583 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____47594 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____47605 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____47618 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____47649 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____47698 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____47732 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____47750 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____47794 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____47838 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____47882 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____47922 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____47952 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____47990 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____48032 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____48070 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____48112 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____48154 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____48214 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____48268 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____48304 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____48335 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____48346 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____48359 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____48381 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____48392 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____48404 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____48435 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____48495 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____48540 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____48578 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____48618 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____48653 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____48706 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____48745 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____48776 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____48821 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____48844 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____48868 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____48899 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____48910 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____48921 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____48932 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____48943 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____48954 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____48965 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____48976 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____48987 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____48998 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____49009 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____49020 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____49031 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____49042 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____49053 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____49064 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____49075 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____49086 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____49097 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____49108 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____49119 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____49130 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____49141 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____49152 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____49163 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____49174 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____49187 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____49210 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____49237 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____49280 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____49313 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____49359 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____49393 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____49404 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____49415 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____49426 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____49437 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____49448 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____49459 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____49470 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____49481 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____49492 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____49541 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____49561 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____49580 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____49600 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____49643 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____49654 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____49670 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____49703 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____49740 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____49804 -> false
  
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
  'Auu____49907 'Auu____49908 'Auu____49909 .
    ('Auu____49907 * 'Auu____49908 * 'Auu____49909) -> 'Auu____49907
  =
  fun uu____49920  ->
    match uu____49920 with | (x,uu____49928,uu____49929) -> x
  
let snd3 :
  'Auu____49939 'Auu____49940 'Auu____49941 .
    ('Auu____49939 * 'Auu____49940 * 'Auu____49941) -> 'Auu____49940
  =
  fun uu____49952  ->
    match uu____49952 with | (uu____49959,x,uu____49961) -> x
  
let thd3 :
  'Auu____49971 'Auu____49972 'Auu____49973 .
    ('Auu____49971 * 'Auu____49972 * 'Auu____49973) -> 'Auu____49973
  =
  fun uu____49984  ->
    match uu____49984 with | (uu____49991,uu____49992,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_50002  ->
    match uu___413_50002 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____50014 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_50024  ->
    match uu___414_50024 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____50033 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_50054  ->
    match uu___415_50054 with
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
    | uu____50099 -> FStar_Pervasives_Native.None
  
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
      let uu___575_50255 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_50255.names_t);
        module_name = (uu___575_50255.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_50269 = env  in
      {
        names = (uu___579_50269.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_50269.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____50284 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____50284 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_50308  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_50315 ->
          let uu____50317 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50317
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_50337  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_50346 ->
          let uu____50348 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50348
  
let add_binders :
  'Auu____50359 . env -> (Prims.string * 'Auu____50359) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____50394  ->
             match uu____50394 with | (name,uu____50401) -> extend env1 name)
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
      | uu____50453 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____50672  ->
    match uu____50672 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____50721 = m  in
               match uu____50721 with
               | (path,uu____50736,uu____50737) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_50755  ->
                  match () with
                  | () ->
                      ((let uu____50759 =
                          let uu____50761 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____50761  in
                        if uu____50759
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____50767 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____50767))) ()
             with
             | e ->
                 ((let uu____50776 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____50776);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____50779  ->
    match uu____50779 with
    | (module_name,modul,uu____50794) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____50829 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_50843  ->
         match uu___416_50843 with
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
         | uu____50854 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____50858 =
      FStar_List.choose
        (fun uu___417_50865  ->
           match uu___417_50865 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____50872 -> FStar_Pervasives_Native.None) flags
       in
    match uu____50858 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____50885 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____50899 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____50901 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____50906) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50933;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____50936;_} when
            FStar_Util.for_some
              (fun uu___418_50941  ->
                 match uu___418_50941 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____50944 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____50965 =
                let uu____50966 =
                  let uu____50987 = translate_cc meta  in
                  let uu____50990 = translate_flags meta  in
                  let uu____50993 = translate_type env t0  in
                  (uu____50987, uu____50990, name1, uu____50993)  in
                DExternal uu____50966  in
              FStar_Pervasives_Native.Some uu____50965
            else
              ((let uu____51009 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____51009);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51015;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____51018;
                FStar_Extraction_ML_Syntax.loc = uu____51019;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51021;_} ->
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
               let rec find_return_type eff i uu___419_51078 =
                 match uu___419_51078 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____51087,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____51107 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____51107 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____51133 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____51133
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____51151) ->
                           let uu____51152 = translate_flags meta  in
                           MustDisappear :: uu____51152
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____51155 = translate_flags meta  in
                           MustDisappear :: uu____51155
                       | uu____51158 -> translate_flags meta  in
                     try
                       (fun uu___780_51167  ->
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
                         ((let uu____51199 =
                             let uu____51205 =
                               let uu____51207 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____51207 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____51205)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____51199);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51233;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51236;_} ->
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
                 (fun uu___807_51273  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____51297 =
                       let uu____51303 =
                         let uu____51305 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____51307 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____51305 uu____51307
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____51303)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____51297);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51325;
            FStar_Extraction_ML_Syntax.mllb_def = uu____51326;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____51327;
            FStar_Extraction_ML_Syntax.print_typ = uu____51328;_} ->
            ((let uu____51335 =
                let uu____51341 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____51341)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____51335);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____51348 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____51348
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____51362 = ty  in
      match uu____51362 with
      | (uu____51365,uu____51366,uu____51367,uu____51368,flags,uu____51370)
          ->
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
                     (let uu____51444 =
                        let uu____51445 =
                          let uu____51465 = translate_flags flags1  in
                          let uu____51468 = translate_type env1 t  in
                          (name1, uu____51465, (FStar_List.length args),
                            uu____51468)
                           in
                        DTypeAlias uu____51445  in
                      FStar_Pervasives_Native.Some uu____51444)
             | (uu____51481,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____51526 =
                   let uu____51527 =
                     let uu____51559 = translate_flags flags1  in
                     let uu____51562 =
                       FStar_List.map
                         (fun uu____51594  ->
                            match uu____51594 with
                            | (f,t) ->
                                let uu____51614 =
                                  let uu____51620 = translate_type env1 t  in
                                  (uu____51620, false)  in
                                (f, uu____51614)) fields
                        in
                     (name1, uu____51559, (FStar_List.length args),
                       uu____51562)
                      in
                   DTypeFlat uu____51527  in
                 FStar_Pervasives_Native.Some uu____51526
             | (uu____51653,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____51703 =
                   let uu____51704 =
                     let uu____51743 =
                       FStar_List.map
                         (fun uu____51796  ->
                            match uu____51796 with
                            | (cons1,ts) ->
                                let uu____51844 =
                                  FStar_List.map
                                    (fun uu____51876  ->
                                       match uu____51876 with
                                       | (name2,t) ->
                                           let uu____51896 =
                                             let uu____51902 =
                                               translate_type env1 t  in
                                             (uu____51902, false)  in
                                           (name2, uu____51896)) ts
                                   in
                                (cons1, uu____51844)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____51743)
                      in
                   DTypeVariant uu____51704  in
                 FStar_Pervasives_Native.Some uu____51703
             | (uu____51955,name,_mangled_name,uu____51958,uu____51959,uu____51960)
                 ->
                 ((let uu____51976 =
                     let uu____51982 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____51982)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____51976);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____51990 = find_t env name  in TBound uu____51990
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____51993,t2) ->
          let uu____51995 =
            let uu____52000 = translate_type env t1  in
            let uu____52001 = translate_type env t2  in
            (uu____52000, uu____52001)  in
          TArrow uu____51995
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____52005 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52005 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____52012 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52012 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____52029 = FStar_Util.must (mk_width m)  in TInt uu____52029
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____52043 = FStar_Util.must (mk_width m)  in TInt uu____52043
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____52048 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52048 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____52052::arg::uu____52054::[],p) when
          (((let uu____52060 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52060 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____52065 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52065 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____52070 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52070 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____52075 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52075 = "FStar.HyperStack.ST.s_mref")
          -> let uu____52079 = translate_type env arg  in TBuf uu____52079
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____52081::[],p) when
          ((((((((((let uu____52087 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52087 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____52092 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52092 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____52097 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52097 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____52102 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52102 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____52107 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52107 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____52112 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52112 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____52117 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52117 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____52122 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52122 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____52127 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52127 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____52132 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52132 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____52137 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52137 = "FStar.HyperStack.ST.mmmref")
          -> let uu____52141 = translate_type env arg  in TBuf uu____52141
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____52143::uu____52144::[],p) when
          let uu____52148 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52148 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____52152 = translate_type env arg  in TBuf uu____52152
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____52159 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52159 = "FStar.Buffer.buffer") ||
                        (let uu____52164 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____52164 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____52169 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____52169 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____52174 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52174 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____52179 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52179 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____52184 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52184 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____52189 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52189 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____52194 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52194 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____52199 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52199 = "FStar.HyperStack.mmref"))
                ||
                (let uu____52204 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52204 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____52209 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52209 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____52214 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52214 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____52219 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52219 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____52224 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52224 = "FStar.HyperStack.ST.mmref")
          -> let uu____52228 = translate_type env arg  in TBuf uu____52228
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52229::arg::[],p) when
          (let uu____52236 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52236 = "FStar.HyperStack.s_ref") ||
            (let uu____52241 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52241 = "FStar.HyperStack.ST.s_ref")
          -> let uu____52245 = translate_type env arg  in TBuf uu____52245
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52246::[],p) when
          let uu____52250 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52250 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____52302 = FStar_List.map (translate_type env) args  in
          TTuple uu____52302
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____52313 =
              let uu____52328 = FStar_List.map (translate_type env) args  in
              (lid, uu____52328)  in
            TApp uu____52313
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____52346 = FStar_List.map (translate_type env) ts  in
          TTuple uu____52346

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
    fun uu____52364  ->
      match uu____52364 with
      | (name,typ) ->
          let uu____52374 = translate_type env typ  in
          { name; typ = uu____52374; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____52381 = find env name  in EBound uu____52381
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____52395 =
            let uu____52400 = FStar_Util.must (mk_op op)  in
            let uu____52401 = FStar_Util.must (mk_width m)  in
            (uu____52400, uu____52401)  in
          EOp uu____52395
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____52411 =
            let uu____52416 = FStar_Util.must (mk_bool_op op)  in
            (uu____52416, Bool)  in
          EOp uu____52411
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
            let uu____52439 = translate_type env typ  in
            { name; typ = uu____52439; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____52466 =
            let uu____52477 = translate_expr env expr  in
            let uu____52478 = translate_branches env branches  in
            (uu____52477, uu____52478)  in
          EMatch uu____52466
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52492;
                  FStar_Extraction_ML_Syntax.loc = uu____52493;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____52495;
             FStar_Extraction_ML_Syntax.loc = uu____52496;_},arg::[])
          when
          let uu____52502 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52502 = "FStar.Dyn.undyn" ->
          let uu____52506 =
            let uu____52511 = translate_expr env arg  in
            let uu____52512 = translate_type env t  in
            (uu____52511, uu____52512)  in
          ECast uu____52506
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52514;
                  FStar_Extraction_ML_Syntax.loc = uu____52515;_},uu____52516);
             FStar_Extraction_ML_Syntax.mlty = uu____52517;
             FStar_Extraction_ML_Syntax.loc = uu____52518;_},uu____52519)
          when
          let uu____52528 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52528 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52533;
                  FStar_Extraction_ML_Syntax.loc = uu____52534;_},uu____52535);
             FStar_Extraction_ML_Syntax.mlty = uu____52536;
             FStar_Extraction_ML_Syntax.loc = uu____52537;_},arg::[])
          when
          ((let uu____52547 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52547 = "FStar.HyperStack.All.failwith") ||
             (let uu____52552 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52552 = "FStar.Error.unexpected"))
            ||
            (let uu____52557 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52557 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____52562;
               FStar_Extraction_ML_Syntax.loc = uu____52563;_} -> EAbortS msg
           | uu____52565 ->
               let print7 =
                 let uu____52567 =
                   let uu____52568 =
                     let uu____52569 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____52569
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____52568  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____52567
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
                  FStar_Extraction_ML_Syntax.mlty = uu____52576;
                  FStar_Extraction_ML_Syntax.loc = uu____52577;_},uu____52578);
             FStar_Extraction_ML_Syntax.mlty = uu____52579;
             FStar_Extraction_ML_Syntax.loc = uu____52580;_},e1::[])
          when
          (let uu____52590 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52590 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____52595 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52595 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52600;
                  FStar_Extraction_ML_Syntax.loc = uu____52601;_},uu____52602);
             FStar_Extraction_ML_Syntax.mlty = uu____52603;
             FStar_Extraction_ML_Syntax.loc = uu____52604;_},e1::e2::[])
          when
          (((let uu____52615 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52615 = "FStar.Buffer.index") ||
              (let uu____52620 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52620 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____52625 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52625 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____52630 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52630 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____52634 =
            let uu____52639 = translate_expr env e1  in
            let uu____52640 = translate_expr env e2  in
            (uu____52639, uu____52640)  in
          EBufRead uu____52634
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52642;
                  FStar_Extraction_ML_Syntax.loc = uu____52643;_},uu____52644);
             FStar_Extraction_ML_Syntax.mlty = uu____52645;
             FStar_Extraction_ML_Syntax.loc = uu____52646;_},e1::[])
          when
          let uu____52654 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52654 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____52658 =
            let uu____52663 = translate_expr env e1  in
            (uu____52663, (EConstant (UInt32, "0")))  in
          EBufRead uu____52658
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52667;
                  FStar_Extraction_ML_Syntax.loc = uu____52668;_},uu____52669);
             FStar_Extraction_ML_Syntax.mlty = uu____52670;
             FStar_Extraction_ML_Syntax.loc = uu____52671;_},e1::e2::[])
          when
          ((let uu____52682 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52682 = "FStar.Buffer.create") ||
             (let uu____52687 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52687 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____52692 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52692 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____52696 =
            let uu____52703 = translate_expr env e1  in
            let uu____52704 = translate_expr env e2  in
            (Stack, uu____52703, uu____52704)  in
          EBufCreate uu____52696
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52706;
                  FStar_Extraction_ML_Syntax.loc = uu____52707;_},uu____52708);
             FStar_Extraction_ML_Syntax.mlty = uu____52709;
             FStar_Extraction_ML_Syntax.loc = uu____52710;_},elen::[])
          when
          let uu____52718 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52718 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____52722 =
            let uu____52727 = translate_expr env elen  in
            (Stack, uu____52727)  in
          EBufCreateNoInit uu____52722
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52729;
                  FStar_Extraction_ML_Syntax.loc = uu____52730;_},uu____52731);
             FStar_Extraction_ML_Syntax.mlty = uu____52732;
             FStar_Extraction_ML_Syntax.loc = uu____52733;_},init1::[])
          when
          let uu____52741 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52741 = "FStar.HyperStack.ST.salloc" ->
          let uu____52745 =
            let uu____52752 = translate_expr env init1  in
            (Stack, uu____52752, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52745
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52756;
                  FStar_Extraction_ML_Syntax.loc = uu____52757;_},uu____52758);
             FStar_Extraction_ML_Syntax.mlty = uu____52759;
             FStar_Extraction_ML_Syntax.loc = uu____52760;_},e2::[])
          when
          ((let uu____52770 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52770 = "FStar.Buffer.createL") ||
             (let uu____52775 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52775 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____52780 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52780 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____52784 =
            let uu____52791 =
              let uu____52794 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52794  in
            (Stack, uu____52791)  in
          EBufCreateL uu____52784
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52800;
                  FStar_Extraction_ML_Syntax.loc = uu____52801;_},uu____52802);
             FStar_Extraction_ML_Syntax.mlty = uu____52803;
             FStar_Extraction_ML_Syntax.loc = uu____52804;_},_erid::e2::[])
          when
          (let uu____52815 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52815 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____52820 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52820 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____52824 =
            let uu____52831 =
              let uu____52834 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52834  in
            (Eternal, uu____52831)  in
          EBufCreateL uu____52824
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52840;
                  FStar_Extraction_ML_Syntax.loc = uu____52841;_},uu____52842);
             FStar_Extraction_ML_Syntax.mlty = uu____52843;
             FStar_Extraction_ML_Syntax.loc = uu____52844;_},_rid::init1::[])
          when
          let uu____52853 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52853 = "FStar.HyperStack.ST.ralloc" ->
          let uu____52857 =
            let uu____52864 = translate_expr env init1  in
            (Eternal, uu____52864, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52857
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52868;
                  FStar_Extraction_ML_Syntax.loc = uu____52869;_},uu____52870);
             FStar_Extraction_ML_Syntax.mlty = uu____52871;
             FStar_Extraction_ML_Syntax.loc = uu____52872;_},_e0::e1::e2::[])
          when
          ((let uu____52884 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52884 = "FStar.Buffer.rcreate") ||
             (let uu____52889 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52889 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____52894 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52894 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____52898 =
            let uu____52905 = translate_expr env e1  in
            let uu____52906 = translate_expr env e2  in
            (Eternal, uu____52905, uu____52906)  in
          EBufCreate uu____52898
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52908;
                  FStar_Extraction_ML_Syntax.loc = uu____52909;_},uu____52910);
             FStar_Extraction_ML_Syntax.mlty = uu____52911;
             FStar_Extraction_ML_Syntax.loc = uu____52912;_},_erid::elen::[])
          when
          let uu____52921 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52921 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____52925 =
            let uu____52930 = translate_expr env elen  in
            (Eternal, uu____52930)  in
          EBufCreateNoInit uu____52925
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52932;
                  FStar_Extraction_ML_Syntax.loc = uu____52933;_},uu____52934);
             FStar_Extraction_ML_Syntax.mlty = uu____52935;
             FStar_Extraction_ML_Syntax.loc = uu____52936;_},_rid::init1::[])
          when
          let uu____52945 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52945 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____52949 =
            let uu____52956 = translate_expr env init1  in
            (ManuallyManaged, uu____52956, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52949
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52960;
                  FStar_Extraction_ML_Syntax.loc = uu____52961;_},uu____52962);
             FStar_Extraction_ML_Syntax.mlty = uu____52963;
             FStar_Extraction_ML_Syntax.loc = uu____52964;_},_e0::e1::e2::[])
          when
          (((let uu____52976 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52976 = "FStar.Buffer.rcreate_mm") ||
              (let uu____52981 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52981 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____52986 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52986 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____52991 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52991 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____52995 =
            let uu____53002 = translate_expr env e1  in
            let uu____53003 = translate_expr env e2  in
            (ManuallyManaged, uu____53002, uu____53003)  in
          EBufCreate uu____52995
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53005;
                  FStar_Extraction_ML_Syntax.loc = uu____53006;_},uu____53007);
             FStar_Extraction_ML_Syntax.mlty = uu____53008;
             FStar_Extraction_ML_Syntax.loc = uu____53009;_},_erid::elen::[])
          when
          let uu____53018 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53018 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____53022 =
            let uu____53027 = translate_expr env elen  in
            (ManuallyManaged, uu____53027)  in
          EBufCreateNoInit uu____53022
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53029;
                  FStar_Extraction_ML_Syntax.loc = uu____53030;_},uu____53031);
             FStar_Extraction_ML_Syntax.mlty = uu____53032;
             FStar_Extraction_ML_Syntax.loc = uu____53033;_},e2::[])
          when
          let uu____53041 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53041 = "FStar.HyperStack.ST.rfree" ->
          let uu____53045 = translate_expr env e2  in EBufFree uu____53045
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53047;
                  FStar_Extraction_ML_Syntax.loc = uu____53048;_},uu____53049);
             FStar_Extraction_ML_Syntax.mlty = uu____53050;
             FStar_Extraction_ML_Syntax.loc = uu____53051;_},e2::[])
          when
          (let uu____53061 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____53061 = "FStar.Buffer.rfree") ||
            (let uu____53066 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53066 = "LowStar.Monotonic.Buffer.free")
          -> let uu____53070 = translate_expr env e2  in EBufFree uu____53070
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53072;
                  FStar_Extraction_ML_Syntax.loc = uu____53073;_},uu____53074);
             FStar_Extraction_ML_Syntax.mlty = uu____53075;
             FStar_Extraction_ML_Syntax.loc = uu____53076;_},e1::e2::_e3::[])
          when
          let uu____53086 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53086 = "FStar.Buffer.sub" ->
          let uu____53090 =
            let uu____53095 = translate_expr env e1  in
            let uu____53096 = translate_expr env e2  in
            (uu____53095, uu____53096)  in
          EBufSub uu____53090
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53098;
                  FStar_Extraction_ML_Syntax.loc = uu____53099;_},uu____53100);
             FStar_Extraction_ML_Syntax.mlty = uu____53101;
             FStar_Extraction_ML_Syntax.loc = uu____53102;_},e1::e2::_e3::[])
          when
          let uu____53112 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53112 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____53116 =
            let uu____53121 = translate_expr env e1  in
            let uu____53122 = translate_expr env e2  in
            (uu____53121, uu____53122)  in
          EBufSub uu____53116
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53124;
                  FStar_Extraction_ML_Syntax.loc = uu____53125;_},uu____53126);
             FStar_Extraction_ML_Syntax.mlty = uu____53127;
             FStar_Extraction_ML_Syntax.loc = uu____53128;_},e1::e2::[])
          when
          let uu____53137 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53137 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53142;
                  FStar_Extraction_ML_Syntax.loc = uu____53143;_},uu____53144);
             FStar_Extraction_ML_Syntax.mlty = uu____53145;
             FStar_Extraction_ML_Syntax.loc = uu____53146;_},e1::e2::[])
          when
          let uu____53155 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53155 = "FStar.Buffer.offset" ->
          let uu____53159 =
            let uu____53164 = translate_expr env e1  in
            let uu____53165 = translate_expr env e2  in
            (uu____53164, uu____53165)  in
          EBufSub uu____53159
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53167;
                  FStar_Extraction_ML_Syntax.loc = uu____53168;_},uu____53169);
             FStar_Extraction_ML_Syntax.mlty = uu____53170;
             FStar_Extraction_ML_Syntax.loc = uu____53171;_},e1::e2::[])
          when
          let uu____53180 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53180 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____53184 =
            let uu____53189 = translate_expr env e1  in
            let uu____53190 = translate_expr env e2  in
            (uu____53189, uu____53190)  in
          EBufSub uu____53184
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53192;
                  FStar_Extraction_ML_Syntax.loc = uu____53193;_},uu____53194);
             FStar_Extraction_ML_Syntax.mlty = uu____53195;
             FStar_Extraction_ML_Syntax.loc = uu____53196;_},e1::e2::e3::[])
          when
          (((let uu____53208 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53208 = "FStar.Buffer.upd") ||
              (let uu____53213 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53213 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____53218 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53218 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____53223 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53223 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____53227 =
            let uu____53234 = translate_expr env e1  in
            let uu____53235 = translate_expr env e2  in
            let uu____53236 = translate_expr env e3  in
            (uu____53234, uu____53235, uu____53236)  in
          EBufWrite uu____53227
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53238;
                  FStar_Extraction_ML_Syntax.loc = uu____53239;_},uu____53240);
             FStar_Extraction_ML_Syntax.mlty = uu____53241;
             FStar_Extraction_ML_Syntax.loc = uu____53242;_},e1::e2::[])
          when
          let uu____53251 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53251 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____53255 =
            let uu____53262 = translate_expr env e1  in
            let uu____53263 = translate_expr env e2  in
            (uu____53262, (EConstant (UInt32, "0")), uu____53263)  in
          EBufWrite uu____53255
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53267;
             FStar_Extraction_ML_Syntax.loc = uu____53268;_},uu____53269::[])
          when
          let uu____53272 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53272 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53277;
             FStar_Extraction_ML_Syntax.loc = uu____53278;_},uu____53279::[])
          when
          let uu____53282 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53282 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53287;
                  FStar_Extraction_ML_Syntax.loc = uu____53288;_},uu____53289);
             FStar_Extraction_ML_Syntax.mlty = uu____53290;
             FStar_Extraction_ML_Syntax.loc = uu____53291;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____53305 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____53305 = "FStar.Buffer.blit") ||
             (let uu____53310 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53310 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____53315 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53315 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____53319 =
            let uu____53330 = translate_expr env e1  in
            let uu____53331 = translate_expr env e2  in
            let uu____53332 = translate_expr env e3  in
            let uu____53333 = translate_expr env e4  in
            let uu____53334 = translate_expr env e5  in
            (uu____53330, uu____53331, uu____53332, uu____53333, uu____53334)
             in
          EBufBlit uu____53319
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53336;
                  FStar_Extraction_ML_Syntax.loc = uu____53337;_},uu____53338);
             FStar_Extraction_ML_Syntax.mlty = uu____53339;
             FStar_Extraction_ML_Syntax.loc = uu____53340;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____53356 =
            let uu____53363 = translate_expr env e1  in
            let uu____53364 = translate_expr env e2  in
            let uu____53365 = translate_expr env e3  in
            (uu____53363, uu____53364, uu____53365)  in
          EBufFill uu____53356
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53367;
             FStar_Extraction_ML_Syntax.loc = uu____53368;_},uu____53369::[])
          when
          let uu____53372 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53372 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53377;
                  FStar_Extraction_ML_Syntax.loc = uu____53378;_},uu____53379);
             FStar_Extraction_ML_Syntax.mlty = uu____53380;
             FStar_Extraction_ML_Syntax.loc = uu____53381;_},_ebuf::_eseq::[])
          when
          (((let uu____53392 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53392 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____53397 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53397 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____53402 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53402 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____53407 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53407 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53412;
             FStar_Extraction_ML_Syntax.loc = uu____53413;_},e1::[])
          when
          let uu____53417 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53417 = "Obj.repr" ->
          let uu____53421 =
            let uu____53426 = translate_expr env e1  in (uu____53426, TAny)
             in
          ECast uu____53421
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53429;
             FStar_Extraction_ML_Syntax.loc = uu____53430;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____53446 = FStar_Util.must (mk_width m)  in
          let uu____53447 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____53446 uu____53447 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53449;
             FStar_Extraction_ML_Syntax.loc = uu____53450;_},args)
          when is_bool_op op ->
          let uu____53464 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____53464 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53466;
             FStar_Extraction_ML_Syntax.loc = uu____53467;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53469;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53470;_}::[])
          when is_machine_int m ->
          let uu____53495 =
            let uu____53501 = FStar_Util.must (mk_width m)  in
            (uu____53501, c)  in
          EConstant uu____53495
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53504;
             FStar_Extraction_ML_Syntax.loc = uu____53505;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53507;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53508;_}::[])
          when is_machine_int m ->
          let uu____53533 =
            let uu____53539 = FStar_Util.must (mk_width m)  in
            (uu____53539, c)  in
          EConstant uu____53533
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53541;
             FStar_Extraction_ML_Syntax.loc = uu____53542;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53544;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53545;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53558 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53560;
             FStar_Extraction_ML_Syntax.loc = uu____53561;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53563;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53564;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53581 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53583;
             FStar_Extraction_ML_Syntax.loc = uu____53584;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53586;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53587;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53602 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53604;
             FStar_Extraction_ML_Syntax.loc = uu____53605;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53607;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53608;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____53623 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____53626;
             FStar_Extraction_ML_Syntax.loc = uu____53627;_},arg::[])
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
            let uu____53655 =
              let uu____53660 = translate_expr env arg  in
              (uu____53660, (TInt UInt64))  in
            ECast uu____53655
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____53665 =
                 let uu____53670 = translate_expr env arg  in
                 (uu____53670, (TInt UInt32))  in
               ECast uu____53665)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____53675 =
                   let uu____53680 = translate_expr env arg  in
                   (uu____53680, (TInt UInt16))  in
                 ECast uu____53675)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____53685 =
                     let uu____53690 = translate_expr env arg  in
                     (uu____53690, (TInt UInt8))  in
                   ECast uu____53685)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____53695 =
                       let uu____53700 = translate_expr env arg  in
                       (uu____53700, (TInt Int64))  in
                     ECast uu____53695)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____53705 =
                         let uu____53710 = translate_expr env arg  in
                         (uu____53710, (TInt Int32))  in
                       ECast uu____53705)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____53715 =
                           let uu____53720 = translate_expr env arg  in
                           (uu____53720, (TInt Int16))  in
                         ECast uu____53715)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____53725 =
                             let uu____53730 = translate_expr env arg  in
                             (uu____53730, (TInt Int8))  in
                           ECast uu____53725)
                        else
                          (let uu____53733 =
                             let uu____53740 =
                               let uu____53743 = translate_expr env arg  in
                               [uu____53743]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____53740)
                              in
                           EApp uu____53733)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____53763 =
            let uu____53770 = translate_expr env head1  in
            let uu____53771 = FStar_List.map (translate_expr env) args  in
            (uu____53770, uu____53771)  in
          EApp uu____53763
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____53782 =
            let uu____53789 = translate_expr env head1  in
            let uu____53790 = FStar_List.map (translate_type env) ty_args  in
            (uu____53789, uu____53790)  in
          ETypApp uu____53782
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____53798 =
            let uu____53803 = translate_expr env e1  in
            let uu____53804 = translate_type env t_to  in
            (uu____53803, uu____53804)  in
          ECast uu____53798
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____53805,fields) ->
          let uu____53827 =
            let uu____53839 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53840 =
              FStar_List.map
                (fun uu____53862  ->
                   match uu____53862 with
                   | (field,expr) ->
                       let uu____53877 = translate_expr env expr  in
                       (field, uu____53877)) fields
               in
            (uu____53839, uu____53840)  in
          EFlat uu____53827
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____53888 =
            let uu____53896 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53897 = translate_expr env e1  in
            (uu____53896, uu____53897, (FStar_Pervasives_Native.snd path))
             in
          EField uu____53888
      | FStar_Extraction_ML_Syntax.MLE_Let uu____53903 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____53916) ->
          let uu____53921 =
            let uu____53923 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____53923
             in
          failwith uu____53921
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____53935 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____53935
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____53941 = FStar_List.map (translate_expr env) es  in
          ETuple uu____53941
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____53944,cons1),es) ->
          let uu____53959 =
            let uu____53969 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53970 = FStar_List.map (translate_expr env) es  in
            (uu____53969, cons1, uu____53970)  in
          ECons uu____53959
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____53996 =
            let uu____54005 = translate_expr env1 body  in
            let uu____54006 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____54005, uu____54006)  in
          EFun uu____53996
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____54016 =
            let uu____54023 = translate_expr env e1  in
            let uu____54024 = translate_expr env e2  in
            let uu____54025 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____54023, uu____54024, uu____54025)  in
          EIfThenElse uu____54016
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____54027 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____54035 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____54051 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____54069 =
              let uu____54084 = FStar_List.map (translate_type env) ts  in
              (lid, uu____54084)  in
            TApp uu____54069
          else TQualified lid
      | uu____54099 -> failwith "invalid argument: assert_lid"

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
    fun uu____54126  ->
      match uu____54126 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____54153 = translate_pat env pat  in
            (match uu____54153 with
             | (env1,pat1) ->
                 let uu____54164 = translate_expr env1 expr  in
                 (pat1, uu____54164))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_54172  ->
    match uu___420_54172 with
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
          let uu____54239 =
            let uu____54240 =
              let uu____54246 = translate_width sw  in (uu____54246, s)  in
            PConstant uu____54240  in
          (env, uu____54239)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____54256,cons1),ps) ->
          let uu____54271 =
            FStar_List.fold_left
              (fun uu____54291  ->
                 fun p1  ->
                   match uu____54291 with
                   | (env1,acc) ->
                       let uu____54311 = translate_pat env1 p1  in
                       (match uu____54311 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54271 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____54341,ps) ->
          let uu____54363 =
            FStar_List.fold_left
              (fun uu____54400  ->
                 fun uu____54401  ->
                   match (uu____54400, uu____54401) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____54481 = translate_pat env1 p1  in
                       (match uu____54481 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____54363 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____54552 =
            FStar_List.fold_left
              (fun uu____54572  ->
                 fun p1  ->
                   match uu____54572 with
                   | (env1,acc) ->
                       let uu____54592 = translate_pat env1 p1  in
                       (match uu____54592 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54552 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____54619 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____54625 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____54639 =
            let uu____54641 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____54641
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____54639
          then
            let uu____54656 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____54656
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____54683) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____54701 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____54703 ->
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
          let uu____54727 =
            let uu____54734 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____54734)  in
          EApp uu____54727
