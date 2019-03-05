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
    match projectee with | DGlobal _0 -> true | uu____46585 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____46697 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____46823 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____46931 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____47064 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____47182 -> false
  
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
    | uu____47324 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____47367 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____47378 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____47389 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____47400 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____47411 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____47422 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____47433 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____47444 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____47457 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____47479 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____47492 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____47516 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____47540 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____47562 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____47573 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____47584 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____47595 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____47606 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____47619 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____47650 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____47699 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____47733 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____47751 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____47795 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____47839 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____47883 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____47923 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____47953 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____47991 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____48033 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____48071 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____48113 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____48155 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____48215 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____48269 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____48305 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____48336 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____48347 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____48360 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____48382 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____48393 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____48405 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____48436 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____48496 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____48541 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____48579 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____48619 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____48654 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____48707 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____48746 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____48777 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____48822 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____48845 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____48869 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____48900 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____48911 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____48922 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____48933 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____48944 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____48955 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____48966 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____48977 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____48988 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____48999 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____49010 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____49021 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____49032 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____49043 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____49054 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____49065 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____49076 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____49087 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____49098 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____49109 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____49120 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____49131 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____49142 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____49153 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____49164 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____49175 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____49188 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____49211 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____49238 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____49281 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____49314 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____49360 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____49394 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____49405 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____49416 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____49427 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____49438 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____49449 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____49460 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____49471 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____49482 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____49493 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____49542 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____49562 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____49581 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____49601 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____49644 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____49655 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____49671 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____49704 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____49741 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____49805 -> false
  
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
  'Auu____49908 'Auu____49909 'Auu____49910 .
    ('Auu____49908 * 'Auu____49909 * 'Auu____49910) -> 'Auu____49908
  =
  fun uu____49921  ->
    match uu____49921 with | (x,uu____49929,uu____49930) -> x
  
let snd3 :
  'Auu____49940 'Auu____49941 'Auu____49942 .
    ('Auu____49940 * 'Auu____49941 * 'Auu____49942) -> 'Auu____49941
  =
  fun uu____49953  ->
    match uu____49953 with | (uu____49960,x,uu____49962) -> x
  
let thd3 :
  'Auu____49972 'Auu____49973 'Auu____49974 .
    ('Auu____49972 * 'Auu____49973 * 'Auu____49974) -> 'Auu____49974
  =
  fun uu____49985  ->
    match uu____49985 with | (uu____49992,uu____49993,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_50003  ->
    match uu___413_50003 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____50015 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_50025  ->
    match uu___414_50025 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____50034 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_50055  ->
    match uu___415_50055 with
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
    | uu____50100 -> FStar_Pervasives_Native.None
  
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
      let uu___575_50256 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_50256.names_t);
        module_name = (uu___575_50256.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_50270 = env  in
      {
        names = (uu___579_50270.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_50270.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____50285 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____50285 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_50309  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_50316 ->
          let uu____50318 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50318
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_50338  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_50347 ->
          let uu____50349 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50349
  
let add_binders :
  'Auu____50360 . env -> (Prims.string * 'Auu____50360) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____50395  ->
             match uu____50395 with | (name,uu____50402) -> extend env1 name)
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
      | uu____50454 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____50673  ->
    match uu____50673 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____50722 = m  in
               match uu____50722 with
               | (path,uu____50737,uu____50738) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_50756  ->
                  match () with
                  | () ->
                      ((let uu____50760 =
                          let uu____50762 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____50762  in
                        if uu____50760
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____50768 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____50768))) ()
             with
             | e ->
                 ((let uu____50777 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____50777);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____50780  ->
    match uu____50780 with
    | (module_name,modul,uu____50795) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____50830 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_50844  ->
         match uu___416_50844 with
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
         | uu____50855 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____50859 =
      FStar_List.choose
        (fun uu___417_50866  ->
           match uu___417_50866 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____50873 -> FStar_Pervasives_Native.None) flags
       in
    match uu____50859 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____50886 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____50900 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____50902 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____50907) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50934;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____50937;_} when
            FStar_Util.for_some
              (fun uu___418_50942  ->
                 match uu___418_50942 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____50945 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____50966 =
                let uu____50967 =
                  let uu____50988 = translate_cc meta  in
                  let uu____50991 = translate_flags meta  in
                  let uu____50994 = translate_type env t0  in
                  (uu____50988, uu____50991, name1, uu____50994)  in
                DExternal uu____50967  in
              FStar_Pervasives_Native.Some uu____50966
            else
              ((let uu____51010 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____51010);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51016;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____51019;
                FStar_Extraction_ML_Syntax.loc = uu____51020;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51022;_} ->
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
               let rec find_return_type eff i uu___419_51079 =
                 match uu___419_51079 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____51088,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____51108 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____51108 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____51134 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____51134
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____51152) ->
                           let uu____51153 = translate_flags meta  in
                           MustDisappear :: uu____51153
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____51156 = translate_flags meta  in
                           MustDisappear :: uu____51156
                       | uu____51159 -> translate_flags meta  in
                     try
                       (fun uu___780_51168  ->
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
                         ((let uu____51200 =
                             let uu____51206 =
                               let uu____51208 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____51208 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____51206)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____51200);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51234;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51237;_} ->
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
                 (fun uu___807_51274  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____51298 =
                       let uu____51304 =
                         let uu____51306 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____51308 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____51306 uu____51308
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____51304)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____51298);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51326;
            FStar_Extraction_ML_Syntax.mllb_def = uu____51327;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____51328;
            FStar_Extraction_ML_Syntax.print_typ = uu____51329;_} ->
            ((let uu____51336 =
                let uu____51342 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____51342)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____51336);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____51349 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____51349
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____51363 = ty  in
      match uu____51363 with
      | (uu____51366,uu____51367,uu____51368,uu____51369,flags,uu____51371)
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
                     (let uu____51445 =
                        let uu____51446 =
                          let uu____51466 = translate_flags flags1  in
                          let uu____51469 = translate_type env1 t  in
                          (name1, uu____51466, (FStar_List.length args),
                            uu____51469)
                           in
                        DTypeAlias uu____51446  in
                      FStar_Pervasives_Native.Some uu____51445)
             | (uu____51482,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____51527 =
                   let uu____51528 =
                     let uu____51560 = translate_flags flags1  in
                     let uu____51563 =
                       FStar_List.map
                         (fun uu____51595  ->
                            match uu____51595 with
                            | (f,t) ->
                                let uu____51615 =
                                  let uu____51621 = translate_type env1 t  in
                                  (uu____51621, false)  in
                                (f, uu____51615)) fields
                        in
                     (name1, uu____51560, (FStar_List.length args),
                       uu____51563)
                      in
                   DTypeFlat uu____51528  in
                 FStar_Pervasives_Native.Some uu____51527
             | (uu____51654,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____51704 =
                   let uu____51705 =
                     let uu____51744 =
                       FStar_List.map
                         (fun uu____51797  ->
                            match uu____51797 with
                            | (cons1,ts) ->
                                let uu____51845 =
                                  FStar_List.map
                                    (fun uu____51877  ->
                                       match uu____51877 with
                                       | (name2,t) ->
                                           let uu____51897 =
                                             let uu____51903 =
                                               translate_type env1 t  in
                                             (uu____51903, false)  in
                                           (name2, uu____51897)) ts
                                   in
                                (cons1, uu____51845)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____51744)
                      in
                   DTypeVariant uu____51705  in
                 FStar_Pervasives_Native.Some uu____51704
             | (uu____51956,name,_mangled_name,uu____51959,uu____51960,uu____51961)
                 ->
                 ((let uu____51977 =
                     let uu____51983 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____51983)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____51977);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____51991 = find_t env name  in TBound uu____51991
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____51994,t2) ->
          let uu____51996 =
            let uu____52001 = translate_type env t1  in
            let uu____52002 = translate_type env t2  in
            (uu____52001, uu____52002)  in
          TArrow uu____51996
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____52006 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52006 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____52013 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52013 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____52030 = FStar_Util.must (mk_width m)  in TInt uu____52030
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____52044 = FStar_Util.must (mk_width m)  in TInt uu____52044
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____52049 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52049 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____52053::arg::uu____52055::[],p) when
          (((let uu____52061 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52061 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____52066 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52066 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____52071 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52071 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____52076 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52076 = "FStar.HyperStack.ST.s_mref")
          -> let uu____52080 = translate_type env arg  in TBuf uu____52080
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____52082::[],p) when
          ((((((((((let uu____52088 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52088 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____52093 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52093 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____52098 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52098 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____52103 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52103 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____52108 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52108 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____52113 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52113 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____52118 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52118 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____52123 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52123 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____52128 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52128 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____52133 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52133 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____52138 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52138 = "FStar.HyperStack.ST.mmmref")
          -> let uu____52142 = translate_type env arg  in TBuf uu____52142
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____52144::uu____52145::[],p) when
          let uu____52149 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52149 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____52153 = translate_type env arg  in TBuf uu____52153
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____52160 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52160 = "FStar.Buffer.buffer") ||
                        (let uu____52165 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____52165 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____52170 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____52170 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____52175 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52175 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____52180 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52180 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____52185 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52185 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____52190 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52190 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____52195 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52195 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____52200 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52200 = "FStar.HyperStack.mmref"))
                ||
                (let uu____52205 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52205 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____52210 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52210 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____52215 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52215 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____52220 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52220 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____52225 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52225 = "FStar.HyperStack.ST.mmref")
          -> let uu____52229 = translate_type env arg  in TBuf uu____52229
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52230::arg::[],p) when
          (let uu____52237 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52237 = "FStar.HyperStack.s_ref") ||
            (let uu____52242 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52242 = "FStar.HyperStack.ST.s_ref")
          -> let uu____52246 = translate_type env arg  in TBuf uu____52246
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52247::[],p) when
          let uu____52251 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52251 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____52303 = FStar_List.map (translate_type env) args  in
          TTuple uu____52303
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____52314 =
              let uu____52329 = FStar_List.map (translate_type env) args  in
              (lid, uu____52329)  in
            TApp uu____52314
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____52347 = FStar_List.map (translate_type env) ts  in
          TTuple uu____52347

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
    fun uu____52365  ->
      match uu____52365 with
      | (name,typ) ->
          let uu____52375 = translate_type env typ  in
          { name; typ = uu____52375; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____52382 = find env name  in EBound uu____52382
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____52396 =
            let uu____52401 = FStar_Util.must (mk_op op)  in
            let uu____52402 = FStar_Util.must (mk_width m)  in
            (uu____52401, uu____52402)  in
          EOp uu____52396
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____52412 =
            let uu____52417 = FStar_Util.must (mk_bool_op op)  in
            (uu____52417, Bool)  in
          EOp uu____52412
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
            let uu____52440 = translate_type env typ  in
            { name; typ = uu____52440; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____52467 =
            let uu____52478 = translate_expr env expr  in
            let uu____52479 = translate_branches env branches  in
            (uu____52478, uu____52479)  in
          EMatch uu____52467
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52493;
                  FStar_Extraction_ML_Syntax.loc = uu____52494;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____52496;
             FStar_Extraction_ML_Syntax.loc = uu____52497;_},arg::[])
          when
          let uu____52503 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52503 = "FStar.Dyn.undyn" ->
          let uu____52507 =
            let uu____52512 = translate_expr env arg  in
            let uu____52513 = translate_type env t  in
            (uu____52512, uu____52513)  in
          ECast uu____52507
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52515;
                  FStar_Extraction_ML_Syntax.loc = uu____52516;_},uu____52517);
             FStar_Extraction_ML_Syntax.mlty = uu____52518;
             FStar_Extraction_ML_Syntax.loc = uu____52519;_},uu____52520)
          when
          let uu____52529 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52529 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52534;
                  FStar_Extraction_ML_Syntax.loc = uu____52535;_},uu____52536);
             FStar_Extraction_ML_Syntax.mlty = uu____52537;
             FStar_Extraction_ML_Syntax.loc = uu____52538;_},arg::[])
          when
          ((let uu____52548 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52548 = "FStar.HyperStack.All.failwith") ||
             (let uu____52553 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52553 = "FStar.Error.unexpected"))
            ||
            (let uu____52558 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52558 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____52563;
               FStar_Extraction_ML_Syntax.loc = uu____52564;_} -> EAbortS msg
           | uu____52566 ->
               let print7 =
                 let uu____52568 =
                   let uu____52569 =
                     let uu____52570 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____52570
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____52569  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____52568
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
                  FStar_Extraction_ML_Syntax.mlty = uu____52577;
                  FStar_Extraction_ML_Syntax.loc = uu____52578;_},uu____52579);
             FStar_Extraction_ML_Syntax.mlty = uu____52580;
             FStar_Extraction_ML_Syntax.loc = uu____52581;_},e1::[])
          when
          (let uu____52591 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52591 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____52596 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52596 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52601;
                  FStar_Extraction_ML_Syntax.loc = uu____52602;_},uu____52603);
             FStar_Extraction_ML_Syntax.mlty = uu____52604;
             FStar_Extraction_ML_Syntax.loc = uu____52605;_},e1::e2::[])
          when
          (((let uu____52616 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52616 = "FStar.Buffer.index") ||
              (let uu____52621 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52621 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____52626 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52626 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____52631 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52631 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____52635 =
            let uu____52640 = translate_expr env e1  in
            let uu____52641 = translate_expr env e2  in
            (uu____52640, uu____52641)  in
          EBufRead uu____52635
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52643;
                  FStar_Extraction_ML_Syntax.loc = uu____52644;_},uu____52645);
             FStar_Extraction_ML_Syntax.mlty = uu____52646;
             FStar_Extraction_ML_Syntax.loc = uu____52647;_},e1::[])
          when
          let uu____52655 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52655 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____52659 =
            let uu____52664 = translate_expr env e1  in
            (uu____52664, (EConstant (UInt32, "0")))  in
          EBufRead uu____52659
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52668;
                  FStar_Extraction_ML_Syntax.loc = uu____52669;_},uu____52670);
             FStar_Extraction_ML_Syntax.mlty = uu____52671;
             FStar_Extraction_ML_Syntax.loc = uu____52672;_},e1::e2::[])
          when
          ((let uu____52683 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52683 = "FStar.Buffer.create") ||
             (let uu____52688 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52688 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____52693 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52693 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____52697 =
            let uu____52704 = translate_expr env e1  in
            let uu____52705 = translate_expr env e2  in
            (Stack, uu____52704, uu____52705)  in
          EBufCreate uu____52697
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52707;
                  FStar_Extraction_ML_Syntax.loc = uu____52708;_},uu____52709);
             FStar_Extraction_ML_Syntax.mlty = uu____52710;
             FStar_Extraction_ML_Syntax.loc = uu____52711;_},elen::[])
          when
          let uu____52719 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52719 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____52723 =
            let uu____52728 = translate_expr env elen  in
            (Stack, uu____52728)  in
          EBufCreateNoInit uu____52723
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52730;
                  FStar_Extraction_ML_Syntax.loc = uu____52731;_},uu____52732);
             FStar_Extraction_ML_Syntax.mlty = uu____52733;
             FStar_Extraction_ML_Syntax.loc = uu____52734;_},init1::[])
          when
          let uu____52742 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52742 = "FStar.HyperStack.ST.salloc" ->
          let uu____52746 =
            let uu____52753 = translate_expr env init1  in
            (Stack, uu____52753, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52746
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52757;
                  FStar_Extraction_ML_Syntax.loc = uu____52758;_},uu____52759);
             FStar_Extraction_ML_Syntax.mlty = uu____52760;
             FStar_Extraction_ML_Syntax.loc = uu____52761;_},e2::[])
          when
          ((let uu____52771 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52771 = "FStar.Buffer.createL") ||
             (let uu____52776 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52776 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____52781 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52781 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____52785 =
            let uu____52792 =
              let uu____52795 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52795  in
            (Stack, uu____52792)  in
          EBufCreateL uu____52785
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52801;
                  FStar_Extraction_ML_Syntax.loc = uu____52802;_},uu____52803);
             FStar_Extraction_ML_Syntax.mlty = uu____52804;
             FStar_Extraction_ML_Syntax.loc = uu____52805;_},_erid::e2::[])
          when
          (let uu____52816 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52816 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____52821 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52821 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____52825 =
            let uu____52832 =
              let uu____52835 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52835  in
            (Eternal, uu____52832)  in
          EBufCreateL uu____52825
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52841;
                  FStar_Extraction_ML_Syntax.loc = uu____52842;_},uu____52843);
             FStar_Extraction_ML_Syntax.mlty = uu____52844;
             FStar_Extraction_ML_Syntax.loc = uu____52845;_},_rid::init1::[])
          when
          let uu____52854 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52854 = "FStar.HyperStack.ST.ralloc" ->
          let uu____52858 =
            let uu____52865 = translate_expr env init1  in
            (Eternal, uu____52865, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52858
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52869;
                  FStar_Extraction_ML_Syntax.loc = uu____52870;_},uu____52871);
             FStar_Extraction_ML_Syntax.mlty = uu____52872;
             FStar_Extraction_ML_Syntax.loc = uu____52873;_},_e0::e1::e2::[])
          when
          ((let uu____52885 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52885 = "FStar.Buffer.rcreate") ||
             (let uu____52890 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52890 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____52895 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52895 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____52899 =
            let uu____52906 = translate_expr env e1  in
            let uu____52907 = translate_expr env e2  in
            (Eternal, uu____52906, uu____52907)  in
          EBufCreate uu____52899
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52909;
                  FStar_Extraction_ML_Syntax.loc = uu____52910;_},uu____52911);
             FStar_Extraction_ML_Syntax.mlty = uu____52912;
             FStar_Extraction_ML_Syntax.loc = uu____52913;_},_erid::elen::[])
          when
          let uu____52922 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52922 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____52926 =
            let uu____52931 = translate_expr env elen  in
            (Eternal, uu____52931)  in
          EBufCreateNoInit uu____52926
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52933;
                  FStar_Extraction_ML_Syntax.loc = uu____52934;_},uu____52935);
             FStar_Extraction_ML_Syntax.mlty = uu____52936;
             FStar_Extraction_ML_Syntax.loc = uu____52937;_},_rid::init1::[])
          when
          let uu____52946 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52946 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____52950 =
            let uu____52957 = translate_expr env init1  in
            (ManuallyManaged, uu____52957, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52950
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52961;
                  FStar_Extraction_ML_Syntax.loc = uu____52962;_},uu____52963);
             FStar_Extraction_ML_Syntax.mlty = uu____52964;
             FStar_Extraction_ML_Syntax.loc = uu____52965;_},_e0::e1::e2::[])
          when
          (((let uu____52977 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52977 = "FStar.Buffer.rcreate_mm") ||
              (let uu____52982 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52982 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____52987 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52987 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____52992 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52992 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____52996 =
            let uu____53003 = translate_expr env e1  in
            let uu____53004 = translate_expr env e2  in
            (ManuallyManaged, uu____53003, uu____53004)  in
          EBufCreate uu____52996
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53006;
                  FStar_Extraction_ML_Syntax.loc = uu____53007;_},uu____53008);
             FStar_Extraction_ML_Syntax.mlty = uu____53009;
             FStar_Extraction_ML_Syntax.loc = uu____53010;_},_erid::elen::[])
          when
          let uu____53019 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53019 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____53023 =
            let uu____53028 = translate_expr env elen  in
            (ManuallyManaged, uu____53028)  in
          EBufCreateNoInit uu____53023
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53030;
                  FStar_Extraction_ML_Syntax.loc = uu____53031;_},uu____53032);
             FStar_Extraction_ML_Syntax.mlty = uu____53033;
             FStar_Extraction_ML_Syntax.loc = uu____53034;_},e2::[])
          when
          let uu____53042 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53042 = "FStar.HyperStack.ST.rfree" ->
          let uu____53046 = translate_expr env e2  in EBufFree uu____53046
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53048;
                  FStar_Extraction_ML_Syntax.loc = uu____53049;_},uu____53050);
             FStar_Extraction_ML_Syntax.mlty = uu____53051;
             FStar_Extraction_ML_Syntax.loc = uu____53052;_},e2::[])
          when
          (let uu____53062 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____53062 = "FStar.Buffer.rfree") ||
            (let uu____53067 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53067 = "LowStar.Monotonic.Buffer.free")
          -> let uu____53071 = translate_expr env e2  in EBufFree uu____53071
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53073;
                  FStar_Extraction_ML_Syntax.loc = uu____53074;_},uu____53075);
             FStar_Extraction_ML_Syntax.mlty = uu____53076;
             FStar_Extraction_ML_Syntax.loc = uu____53077;_},e1::e2::_e3::[])
          when
          let uu____53087 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53087 = "FStar.Buffer.sub" ->
          let uu____53091 =
            let uu____53096 = translate_expr env e1  in
            let uu____53097 = translate_expr env e2  in
            (uu____53096, uu____53097)  in
          EBufSub uu____53091
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53099;
                  FStar_Extraction_ML_Syntax.loc = uu____53100;_},uu____53101);
             FStar_Extraction_ML_Syntax.mlty = uu____53102;
             FStar_Extraction_ML_Syntax.loc = uu____53103;_},e1::e2::_e3::[])
          when
          let uu____53113 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53113 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____53117 =
            let uu____53122 = translate_expr env e1  in
            let uu____53123 = translate_expr env e2  in
            (uu____53122, uu____53123)  in
          EBufSub uu____53117
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53125;
                  FStar_Extraction_ML_Syntax.loc = uu____53126;_},uu____53127);
             FStar_Extraction_ML_Syntax.mlty = uu____53128;
             FStar_Extraction_ML_Syntax.loc = uu____53129;_},e1::e2::[])
          when
          let uu____53138 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53138 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53143;
                  FStar_Extraction_ML_Syntax.loc = uu____53144;_},uu____53145);
             FStar_Extraction_ML_Syntax.mlty = uu____53146;
             FStar_Extraction_ML_Syntax.loc = uu____53147;_},e1::e2::[])
          when
          let uu____53156 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53156 = "FStar.Buffer.offset" ->
          let uu____53160 =
            let uu____53165 = translate_expr env e1  in
            let uu____53166 = translate_expr env e2  in
            (uu____53165, uu____53166)  in
          EBufSub uu____53160
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53168;
                  FStar_Extraction_ML_Syntax.loc = uu____53169;_},uu____53170);
             FStar_Extraction_ML_Syntax.mlty = uu____53171;
             FStar_Extraction_ML_Syntax.loc = uu____53172;_},e1::e2::[])
          when
          let uu____53181 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53181 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____53185 =
            let uu____53190 = translate_expr env e1  in
            let uu____53191 = translate_expr env e2  in
            (uu____53190, uu____53191)  in
          EBufSub uu____53185
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53193;
                  FStar_Extraction_ML_Syntax.loc = uu____53194;_},uu____53195);
             FStar_Extraction_ML_Syntax.mlty = uu____53196;
             FStar_Extraction_ML_Syntax.loc = uu____53197;_},e1::e2::e3::[])
          when
          (((let uu____53209 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53209 = "FStar.Buffer.upd") ||
              (let uu____53214 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53214 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____53219 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53219 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____53224 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53224 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____53228 =
            let uu____53235 = translate_expr env e1  in
            let uu____53236 = translate_expr env e2  in
            let uu____53237 = translate_expr env e3  in
            (uu____53235, uu____53236, uu____53237)  in
          EBufWrite uu____53228
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53239;
                  FStar_Extraction_ML_Syntax.loc = uu____53240;_},uu____53241);
             FStar_Extraction_ML_Syntax.mlty = uu____53242;
             FStar_Extraction_ML_Syntax.loc = uu____53243;_},e1::e2::[])
          when
          let uu____53252 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53252 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____53256 =
            let uu____53263 = translate_expr env e1  in
            let uu____53264 = translate_expr env e2  in
            (uu____53263, (EConstant (UInt32, "0")), uu____53264)  in
          EBufWrite uu____53256
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53268;
             FStar_Extraction_ML_Syntax.loc = uu____53269;_},uu____53270::[])
          when
          let uu____53273 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53273 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53278;
             FStar_Extraction_ML_Syntax.loc = uu____53279;_},uu____53280::[])
          when
          let uu____53283 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53283 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53288;
                  FStar_Extraction_ML_Syntax.loc = uu____53289;_},uu____53290);
             FStar_Extraction_ML_Syntax.mlty = uu____53291;
             FStar_Extraction_ML_Syntax.loc = uu____53292;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____53306 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____53306 = "FStar.Buffer.blit") ||
             (let uu____53311 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53311 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____53316 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53316 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____53320 =
            let uu____53331 = translate_expr env e1  in
            let uu____53332 = translate_expr env e2  in
            let uu____53333 = translate_expr env e3  in
            let uu____53334 = translate_expr env e4  in
            let uu____53335 = translate_expr env e5  in
            (uu____53331, uu____53332, uu____53333, uu____53334, uu____53335)
             in
          EBufBlit uu____53320
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53337;
                  FStar_Extraction_ML_Syntax.loc = uu____53338;_},uu____53339);
             FStar_Extraction_ML_Syntax.mlty = uu____53340;
             FStar_Extraction_ML_Syntax.loc = uu____53341;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____53357 =
            let uu____53364 = translate_expr env e1  in
            let uu____53365 = translate_expr env e2  in
            let uu____53366 = translate_expr env e3  in
            (uu____53364, uu____53365, uu____53366)  in
          EBufFill uu____53357
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53368;
             FStar_Extraction_ML_Syntax.loc = uu____53369;_},uu____53370::[])
          when
          let uu____53373 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53373 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53378;
                  FStar_Extraction_ML_Syntax.loc = uu____53379;_},uu____53380);
             FStar_Extraction_ML_Syntax.mlty = uu____53381;
             FStar_Extraction_ML_Syntax.loc = uu____53382;_},_ebuf::_eseq::[])
          when
          (((let uu____53393 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53393 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____53398 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53398 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____53403 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53403 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____53408 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53408 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53413;
             FStar_Extraction_ML_Syntax.loc = uu____53414;_},e1::[])
          when
          let uu____53418 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53418 = "Obj.repr" ->
          let uu____53422 =
            let uu____53427 = translate_expr env e1  in (uu____53427, TAny)
             in
          ECast uu____53422
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53430;
             FStar_Extraction_ML_Syntax.loc = uu____53431;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____53447 = FStar_Util.must (mk_width m)  in
          let uu____53448 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____53447 uu____53448 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53450;
             FStar_Extraction_ML_Syntax.loc = uu____53451;_},args)
          when is_bool_op op ->
          let uu____53465 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____53465 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53467;
             FStar_Extraction_ML_Syntax.loc = uu____53468;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53470;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53471;_}::[])
          when is_machine_int m ->
          let uu____53496 =
            let uu____53502 = FStar_Util.must (mk_width m)  in
            (uu____53502, c)  in
          EConstant uu____53496
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53505;
             FStar_Extraction_ML_Syntax.loc = uu____53506;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53508;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53509;_}::[])
          when is_machine_int m ->
          let uu____53534 =
            let uu____53540 = FStar_Util.must (mk_width m)  in
            (uu____53540, c)  in
          EConstant uu____53534
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53542;
             FStar_Extraction_ML_Syntax.loc = uu____53543;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53545;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53546;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53559 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53561;
             FStar_Extraction_ML_Syntax.loc = uu____53562;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53564;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53565;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53582 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53584;
             FStar_Extraction_ML_Syntax.loc = uu____53585;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53587;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53588;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53603 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53605;
             FStar_Extraction_ML_Syntax.loc = uu____53606;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53608;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53609;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____53624 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____53627;
             FStar_Extraction_ML_Syntax.loc = uu____53628;_},arg::[])
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
            let uu____53656 =
              let uu____53661 = translate_expr env arg  in
              (uu____53661, (TInt UInt64))  in
            ECast uu____53656
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____53666 =
                 let uu____53671 = translate_expr env arg  in
                 (uu____53671, (TInt UInt32))  in
               ECast uu____53666)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____53676 =
                   let uu____53681 = translate_expr env arg  in
                   (uu____53681, (TInt UInt16))  in
                 ECast uu____53676)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____53686 =
                     let uu____53691 = translate_expr env arg  in
                     (uu____53691, (TInt UInt8))  in
                   ECast uu____53686)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____53696 =
                       let uu____53701 = translate_expr env arg  in
                       (uu____53701, (TInt Int64))  in
                     ECast uu____53696)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____53706 =
                         let uu____53711 = translate_expr env arg  in
                         (uu____53711, (TInt Int32))  in
                       ECast uu____53706)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____53716 =
                           let uu____53721 = translate_expr env arg  in
                           (uu____53721, (TInt Int16))  in
                         ECast uu____53716)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____53726 =
                             let uu____53731 = translate_expr env arg  in
                             (uu____53731, (TInt Int8))  in
                           ECast uu____53726)
                        else
                          (let uu____53734 =
                             let uu____53741 =
                               let uu____53744 = translate_expr env arg  in
                               [uu____53744]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____53741)
                              in
                           EApp uu____53734)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____53764 =
            let uu____53771 = translate_expr env head1  in
            let uu____53772 = FStar_List.map (translate_expr env) args  in
            (uu____53771, uu____53772)  in
          EApp uu____53764
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____53783 =
            let uu____53790 = translate_expr env head1  in
            let uu____53791 = FStar_List.map (translate_type env) ty_args  in
            (uu____53790, uu____53791)  in
          ETypApp uu____53783
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____53799 =
            let uu____53804 = translate_expr env e1  in
            let uu____53805 = translate_type env t_to  in
            (uu____53804, uu____53805)  in
          ECast uu____53799
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____53806,fields) ->
          let uu____53828 =
            let uu____53840 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53841 =
              FStar_List.map
                (fun uu____53863  ->
                   match uu____53863 with
                   | (field,expr) ->
                       let uu____53878 = translate_expr env expr  in
                       (field, uu____53878)) fields
               in
            (uu____53840, uu____53841)  in
          EFlat uu____53828
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____53889 =
            let uu____53897 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53898 = translate_expr env e1  in
            (uu____53897, uu____53898, (FStar_Pervasives_Native.snd path))
             in
          EField uu____53889
      | FStar_Extraction_ML_Syntax.MLE_Let uu____53904 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____53917) ->
          let uu____53922 =
            let uu____53924 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____53924
             in
          failwith uu____53922
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____53936 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____53936
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____53942 = FStar_List.map (translate_expr env) es  in
          ETuple uu____53942
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____53945,cons1),es) ->
          let uu____53960 =
            let uu____53970 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53971 = FStar_List.map (translate_expr env) es  in
            (uu____53970, cons1, uu____53971)  in
          ECons uu____53960
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____53997 =
            let uu____54006 = translate_expr env1 body  in
            let uu____54007 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____54006, uu____54007)  in
          EFun uu____53997
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____54017 =
            let uu____54024 = translate_expr env e1  in
            let uu____54025 = translate_expr env e2  in
            let uu____54026 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____54024, uu____54025, uu____54026)  in
          EIfThenElse uu____54017
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____54028 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____54036 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____54052 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____54070 =
              let uu____54085 = FStar_List.map (translate_type env) ts  in
              (lid, uu____54085)  in
            TApp uu____54070
          else TQualified lid
      | uu____54100 -> failwith "invalid argument: assert_lid"

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
    fun uu____54127  ->
      match uu____54127 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____54154 = translate_pat env pat  in
            (match uu____54154 with
             | (env1,pat1) ->
                 let uu____54165 = translate_expr env1 expr  in
                 (pat1, uu____54165))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_54173  ->
    match uu___420_54173 with
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
          let uu____54240 =
            let uu____54241 =
              let uu____54247 = translate_width sw  in (uu____54247, s)  in
            PConstant uu____54241  in
          (env, uu____54240)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____54257,cons1),ps) ->
          let uu____54272 =
            FStar_List.fold_left
              (fun uu____54292  ->
                 fun p1  ->
                   match uu____54292 with
                   | (env1,acc) ->
                       let uu____54312 = translate_pat env1 p1  in
                       (match uu____54312 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54272 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____54342,ps) ->
          let uu____54364 =
            FStar_List.fold_left
              (fun uu____54401  ->
                 fun uu____54402  ->
                   match (uu____54401, uu____54402) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____54482 = translate_pat env1 p1  in
                       (match uu____54482 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____54364 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____54553 =
            FStar_List.fold_left
              (fun uu____54573  ->
                 fun p1  ->
                   match uu____54573 with
                   | (env1,acc) ->
                       let uu____54593 = translate_pat env1 p1  in
                       (match uu____54593 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54553 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____54620 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____54626 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____54640 =
            let uu____54642 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____54642
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____54640
          then
            let uu____54657 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____54657
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____54684) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____54702 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____54704 ->
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
          let uu____54728 =
            let uu____54735 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____54735)  in
          EApp uu____54728
