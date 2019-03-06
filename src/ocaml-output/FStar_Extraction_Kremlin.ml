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
    match projectee with | DGlobal _0 -> true | uu____42724 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____42836 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____42962 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____43070 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____43203 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____43321 -> false
  
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
    | uu____43463 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____43506 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____43517 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____43528 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____43539 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____43550 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____43561 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____43572 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____43583 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____43596 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____43618 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____43631 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____43655 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____43679 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____43701 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____43712 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____43723 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____43734 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____43745 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____43758 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____43789 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____43838 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____43872 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____43890 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____43934 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____43978 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____44022 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____44062 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____44092 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____44130 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____44172 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____44210 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____44252 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____44294 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____44354 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____44408 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____44444 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____44475 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____44486 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____44499 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____44521 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____44532 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____44544 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____44575 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____44635 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____44680 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____44718 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____44758 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____44793 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____44846 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____44885 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____44916 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____44961 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____44984 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____45008 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____45039 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____45050 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____45061 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____45072 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____45083 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____45094 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____45105 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____45116 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____45127 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____45138 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____45149 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____45160 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____45171 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____45182 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____45193 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____45204 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____45215 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____45226 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____45237 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____45248 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____45259 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____45270 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____45281 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____45292 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____45303 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____45314 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____45327 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____45350 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____45377 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____45420 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____45453 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____45499 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____45533 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____45544 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____45555 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____45566 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____45577 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____45588 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____45599 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____45610 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____45621 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____45632 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____45681 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____45701 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____45720 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____45740 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____45783 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____45794 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____45810 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____45843 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____45880 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____45944 -> false
  
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
  'Auu____46046 'Auu____46047 'Auu____46048 .
    ('Auu____46046 * 'Auu____46047 * 'Auu____46048) -> 'Auu____46046
  =
  fun uu____46059  ->
    match uu____46059 with | (x,uu____46067,uu____46068) -> x
  
let snd3 :
  'Auu____46078 'Auu____46079 'Auu____46080 .
    ('Auu____46078 * 'Auu____46079 * 'Auu____46080) -> 'Auu____46079
  =
  fun uu____46091  ->
    match uu____46091 with | (uu____46098,x,uu____46100) -> x
  
let thd3 :
  'Auu____46110 'Auu____46111 'Auu____46112 .
    ('Auu____46110 * 'Auu____46111 * 'Auu____46112) -> 'Auu____46112
  =
  fun uu____46123  ->
    match uu____46123 with | (uu____46130,uu____46131,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_46141  ->
    match uu___413_46141 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____46153 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_46163  ->
    match uu___414_46163 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____46172 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_46193  ->
    match uu___415_46193 with
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
    | uu____46238 -> FStar_Pervasives_Native.None
  
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
      let uu___575_46394 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_46394.names_t);
        module_name = (uu___575_46394.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_46408 = env  in
      {
        names = (uu___579_46408.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_46408.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____46423 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____46423 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_46447  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_46454 ->
          let uu____46456 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____46456
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_46476  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_46485 ->
          let uu____46487 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____46487
  
let add_binders :
  'Auu____46498 . env -> (Prims.string * 'Auu____46498) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____46533  ->
             match uu____46533 with | (name,uu____46540) -> extend env1 name)
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
      | uu____46592 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____46811  ->
    match uu____46811 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____46860 = m  in
               match uu____46860 with
               | (path,uu____46875,uu____46876) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_46894  ->
                  match () with
                  | () ->
                      ((let uu____46898 =
                          let uu____46900 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____46900  in
                        if uu____46898
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____46906 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____46906))) ()
             with
             | e ->
                 ((let uu____46915 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____46915);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____46918  ->
    match uu____46918 with
    | (module_name,modul,uu____46933) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____46968 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_46982  ->
         match uu___416_46982 with
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
         | uu____46993 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____46997 =
      FStar_List.choose
        (fun uu___417_47004  ->
           match uu___417_47004 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____47011 -> FStar_Pervasives_Native.None) flags
       in
    match uu____46997 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____47024 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____47038 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____47040 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____47045) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____47072;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____47075;_} when
            FStar_Util.for_some
              (fun uu___418_47080  ->
                 match uu___418_47080 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____47083 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____47104 =
                let uu____47105 =
                  let uu____47126 = translate_cc meta  in
                  let uu____47129 = translate_flags meta  in
                  let uu____47132 = translate_type env t0  in
                  (uu____47126, uu____47129, name1, uu____47132)  in
                DExternal uu____47105  in
              FStar_Pervasives_Native.Some uu____47104
            else
              ((let uu____47148 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____47148);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____47154;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____47157;
                FStar_Extraction_ML_Syntax.loc = uu____47158;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____47160;_} ->
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
               let rec find_return_type eff i uu___419_47217 =
                 match uu___419_47217 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____47226,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____47246 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____47246 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____47272 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____47272
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____47290) ->
                           let uu____47291 = translate_flags meta  in
                           MustDisappear :: uu____47291
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____47294 = translate_flags meta  in
                           MustDisappear :: uu____47294
                       | uu____47297 -> translate_flags meta  in
                     try
                       (fun uu___780_47306  ->
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
                         ((let uu____47338 =
                             let uu____47344 =
                               let uu____47346 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____47346 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____47344)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____47338);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____47372;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____47375;_} ->
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
                 (fun uu___807_47412  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____47436 =
                       let uu____47442 =
                         let uu____47444 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____47446 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____47444 uu____47446
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____47442)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____47436);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____47464;
            FStar_Extraction_ML_Syntax.mllb_def = uu____47465;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____47466;
            FStar_Extraction_ML_Syntax.print_typ = uu____47467;_} ->
            ((let uu____47474 =
                let uu____47480 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____47480)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____47474);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____47487 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____47487
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____47501 = ty  in
      match uu____47501 with
      | (uu____47504,uu____47505,uu____47506,uu____47507,flags,uu____47509)
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
                     (let uu____47583 =
                        let uu____47584 =
                          let uu____47604 = translate_flags flags1  in
                          let uu____47607 = translate_type env1 t  in
                          (name1, uu____47604, (FStar_List.length args),
                            uu____47607)
                           in
                        DTypeAlias uu____47584  in
                      FStar_Pervasives_Native.Some uu____47583)
             | (uu____47620,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____47665 =
                   let uu____47666 =
                     let uu____47698 = translate_flags flags1  in
                     let uu____47701 =
                       FStar_List.map
                         (fun uu____47733  ->
                            match uu____47733 with
                            | (f,t) ->
                                let uu____47753 =
                                  let uu____47759 = translate_type env1 t  in
                                  (uu____47759, false)  in
                                (f, uu____47753)) fields
                        in
                     (name1, uu____47698, (FStar_List.length args),
                       uu____47701)
                      in
                   DTypeFlat uu____47666  in
                 FStar_Pervasives_Native.Some uu____47665
             | (uu____47792,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____47842 =
                   let uu____47843 =
                     let uu____47882 =
                       FStar_List.map
                         (fun uu____47935  ->
                            match uu____47935 with
                            | (cons1,ts) ->
                                let uu____47983 =
                                  FStar_List.map
                                    (fun uu____48015  ->
                                       match uu____48015 with
                                       | (name2,t) ->
                                           let uu____48035 =
                                             let uu____48041 =
                                               translate_type env1 t  in
                                             (uu____48041, false)  in
                                           (name2, uu____48035)) ts
                                   in
                                (cons1, uu____47983)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____47882)
                      in
                   DTypeVariant uu____47843  in
                 FStar_Pervasives_Native.Some uu____47842
             | (uu____48094,name,_mangled_name,uu____48097,uu____48098,uu____48099)
                 ->
                 ((let uu____48115 =
                     let uu____48121 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____48121)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____48115);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____48129 = find_t env name  in TBound uu____48129
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____48132,t2) ->
          let uu____48134 =
            let uu____48139 = translate_type env t1  in
            let uu____48140 = translate_type env t2  in
            (uu____48139, uu____48140)  in
          TArrow uu____48134
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____48144 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48144 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____48151 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48151 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____48168 = FStar_Util.must (mk_width m)  in TInt uu____48168
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____48182 = FStar_Util.must (mk_width m)  in TInt uu____48182
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____48187 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48187 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____48191::arg::uu____48193::[],p) when
          (((let uu____48199 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48199 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____48204 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48204 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____48209 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48209 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____48214 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48214 = "FStar.HyperStack.ST.s_mref")
          -> let uu____48218 = translate_type env arg  in TBuf uu____48218
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____48220::[],p) when
          ((((((((((let uu____48226 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____48226 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____48231 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____48231 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____48236 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____48236 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____48241 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____48241 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____48246 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____48246 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____48251 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____48251 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____48256 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____48256 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____48261 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____48261 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____48266 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48266 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____48271 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48271 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____48276 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48276 = "FStar.HyperStack.ST.mmmref")
          -> let uu____48280 = translate_type env arg  in TBuf uu____48280
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____48282::uu____48283::[],p) when
          let uu____48287 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48287 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____48291 = translate_type env arg  in TBuf uu____48291
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____48298 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____48298 = "FStar.Buffer.buffer") ||
                        (let uu____48303 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____48303 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____48308 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____48308 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____48313 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____48313 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____48318 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____48318 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____48323 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____48323 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____48328 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____48328 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____48333 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____48333 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____48338 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____48338 = "FStar.HyperStack.mmref"))
                ||
                (let uu____48343 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____48343 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____48348 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____48348 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____48353 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48353 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____48358 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48358 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____48363 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48363 = "FStar.HyperStack.ST.mmref")
          -> let uu____48367 = translate_type env arg  in TBuf uu____48367
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____48368::arg::[],p) when
          (let uu____48375 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48375 = "FStar.HyperStack.s_ref") ||
            (let uu____48380 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48380 = "FStar.HyperStack.ST.s_ref")
          -> let uu____48384 = translate_type env arg  in TBuf uu____48384
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____48385::[],p) when
          let uu____48389 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48389 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____48441 = FStar_List.map (translate_type env) args  in
          TTuple uu____48441
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____48452 =
              let uu____48467 = FStar_List.map (translate_type env) args  in
              (lid, uu____48467)  in
            TApp uu____48452
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____48485 = FStar_List.map (translate_type env) ts  in
          TTuple uu____48485

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
    fun uu____48503  ->
      match uu____48503 with
      | (name,typ) ->
          let uu____48513 = translate_type env typ  in
          { name; typ = uu____48513; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____48520 = find env name  in EBound uu____48520
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____48534 =
            let uu____48539 = FStar_Util.must (mk_op op)  in
            let uu____48540 = FStar_Util.must (mk_width m)  in
            (uu____48539, uu____48540)  in
          EOp uu____48534
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____48550 =
            let uu____48555 = FStar_Util.must (mk_bool_op op)  in
            (uu____48555, Bool)  in
          EOp uu____48550
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
            let uu____48578 = translate_type env typ  in
            { name; typ = uu____48578; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____48605 =
            let uu____48616 = translate_expr env expr  in
            let uu____48617 = translate_branches env branches  in
            (uu____48616, uu____48617)  in
          EMatch uu____48605
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48631;
                  FStar_Extraction_ML_Syntax.loc = uu____48632;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____48634;
             FStar_Extraction_ML_Syntax.loc = uu____48635;_},arg::[])
          when
          let uu____48641 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48641 = "FStar.Dyn.undyn" ->
          let uu____48645 =
            let uu____48650 = translate_expr env arg  in
            let uu____48651 = translate_type env t  in
            (uu____48650, uu____48651)  in
          ECast uu____48645
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48653;
                  FStar_Extraction_ML_Syntax.loc = uu____48654;_},uu____48655);
             FStar_Extraction_ML_Syntax.mlty = uu____48656;
             FStar_Extraction_ML_Syntax.loc = uu____48657;_},uu____48658)
          when
          let uu____48667 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48667 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48672;
                  FStar_Extraction_ML_Syntax.loc = uu____48673;_},uu____48674);
             FStar_Extraction_ML_Syntax.mlty = uu____48675;
             FStar_Extraction_ML_Syntax.loc = uu____48676;_},arg::[])
          when
          ((let uu____48686 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48686 = "FStar.HyperStack.All.failwith") ||
             (let uu____48691 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48691 = "FStar.Error.unexpected"))
            ||
            (let uu____48696 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48696 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____48701;
               FStar_Extraction_ML_Syntax.loc = uu____48702;_} -> EAbortS msg
           | uu____48704 ->
               let print7 =
                 let uu____48706 =
                   let uu____48707 =
                     let uu____48708 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____48708
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____48707  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____48706
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
                  FStar_Extraction_ML_Syntax.mlty = uu____48715;
                  FStar_Extraction_ML_Syntax.loc = uu____48716;_},uu____48717);
             FStar_Extraction_ML_Syntax.mlty = uu____48718;
             FStar_Extraction_ML_Syntax.loc = uu____48719;_},e1::[])
          when
          (let uu____48729 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48729 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____48734 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48734 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48739;
                  FStar_Extraction_ML_Syntax.loc = uu____48740;_},uu____48741);
             FStar_Extraction_ML_Syntax.mlty = uu____48742;
             FStar_Extraction_ML_Syntax.loc = uu____48743;_},e1::e2::[])
          when
          (((let uu____48754 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48754 = "FStar.Buffer.index") ||
              (let uu____48759 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48759 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____48764 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48764 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____48769 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48769 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____48773 =
            let uu____48778 = translate_expr env e1  in
            let uu____48779 = translate_expr env e2  in
            (uu____48778, uu____48779)  in
          EBufRead uu____48773
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48781;
                  FStar_Extraction_ML_Syntax.loc = uu____48782;_},uu____48783);
             FStar_Extraction_ML_Syntax.mlty = uu____48784;
             FStar_Extraction_ML_Syntax.loc = uu____48785;_},e1::[])
          when
          let uu____48793 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48793 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____48797 =
            let uu____48802 = translate_expr env e1  in
            (uu____48802, (EConstant (UInt32, "0")))  in
          EBufRead uu____48797
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48806;
                  FStar_Extraction_ML_Syntax.loc = uu____48807;_},uu____48808);
             FStar_Extraction_ML_Syntax.mlty = uu____48809;
             FStar_Extraction_ML_Syntax.loc = uu____48810;_},e1::e2::[])
          when
          ((let uu____48821 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48821 = "FStar.Buffer.create") ||
             (let uu____48826 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48826 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____48831 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48831 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____48835 =
            let uu____48842 = translate_expr env e1  in
            let uu____48843 = translate_expr env e2  in
            (Stack, uu____48842, uu____48843)  in
          EBufCreate uu____48835
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48845;
                  FStar_Extraction_ML_Syntax.loc = uu____48846;_},uu____48847);
             FStar_Extraction_ML_Syntax.mlty = uu____48848;
             FStar_Extraction_ML_Syntax.loc = uu____48849;_},elen::[])
          when
          let uu____48857 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48857 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____48861 =
            let uu____48866 = translate_expr env elen  in
            (Stack, uu____48866)  in
          EBufCreateNoInit uu____48861
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48868;
                  FStar_Extraction_ML_Syntax.loc = uu____48869;_},uu____48870);
             FStar_Extraction_ML_Syntax.mlty = uu____48871;
             FStar_Extraction_ML_Syntax.loc = uu____48872;_},init1::[])
          when
          let uu____48880 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48880 = "FStar.HyperStack.ST.salloc" ->
          let uu____48884 =
            let uu____48891 = translate_expr env init1  in
            (Stack, uu____48891, (EConstant (UInt32, "1")))  in
          EBufCreate uu____48884
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48895;
                  FStar_Extraction_ML_Syntax.loc = uu____48896;_},uu____48897);
             FStar_Extraction_ML_Syntax.mlty = uu____48898;
             FStar_Extraction_ML_Syntax.loc = uu____48899;_},e2::[])
          when
          ((let uu____48909 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48909 = "FStar.Buffer.createL") ||
             (let uu____48914 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48914 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____48919 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48919 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____48923 =
            let uu____48930 =
              let uu____48933 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____48933  in
            (Stack, uu____48930)  in
          EBufCreateL uu____48923
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48939;
                  FStar_Extraction_ML_Syntax.loc = uu____48940;_},uu____48941);
             FStar_Extraction_ML_Syntax.mlty = uu____48942;
             FStar_Extraction_ML_Syntax.loc = uu____48943;_},_erid::e2::[])
          when
          (let uu____48954 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48954 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____48959 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48959 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____48963 =
            let uu____48970 =
              let uu____48973 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____48973  in
            (Eternal, uu____48970)  in
          EBufCreateL uu____48963
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48979;
                  FStar_Extraction_ML_Syntax.loc = uu____48980;_},uu____48981);
             FStar_Extraction_ML_Syntax.mlty = uu____48982;
             FStar_Extraction_ML_Syntax.loc = uu____48983;_},_rid::init1::[])
          when
          let uu____48992 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48992 = "FStar.HyperStack.ST.ralloc" ->
          let uu____48996 =
            let uu____49003 = translate_expr env init1  in
            (Eternal, uu____49003, (EConstant (UInt32, "1")))  in
          EBufCreate uu____48996
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49007;
                  FStar_Extraction_ML_Syntax.loc = uu____49008;_},uu____49009);
             FStar_Extraction_ML_Syntax.mlty = uu____49010;
             FStar_Extraction_ML_Syntax.loc = uu____49011;_},_e0::e1::e2::[])
          when
          ((let uu____49023 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____49023 = "FStar.Buffer.rcreate") ||
             (let uu____49028 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____49028 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____49033 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49033 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____49037 =
            let uu____49044 = translate_expr env e1  in
            let uu____49045 = translate_expr env e2  in
            (Eternal, uu____49044, uu____49045)  in
          EBufCreate uu____49037
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49047;
                  FStar_Extraction_ML_Syntax.loc = uu____49048;_},uu____49049);
             FStar_Extraction_ML_Syntax.mlty = uu____49050;
             FStar_Extraction_ML_Syntax.loc = uu____49051;_},_erid::elen::[])
          when
          let uu____49060 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49060 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____49064 =
            let uu____49069 = translate_expr env elen  in
            (Eternal, uu____49069)  in
          EBufCreateNoInit uu____49064
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49071;
                  FStar_Extraction_ML_Syntax.loc = uu____49072;_},uu____49073);
             FStar_Extraction_ML_Syntax.mlty = uu____49074;
             FStar_Extraction_ML_Syntax.loc = uu____49075;_},_rid::init1::[])
          when
          let uu____49084 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49084 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____49088 =
            let uu____49095 = translate_expr env init1  in
            (ManuallyManaged, uu____49095, (EConstant (UInt32, "1")))  in
          EBufCreate uu____49088
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49099;
                  FStar_Extraction_ML_Syntax.loc = uu____49100;_},uu____49101);
             FStar_Extraction_ML_Syntax.mlty = uu____49102;
             FStar_Extraction_ML_Syntax.loc = uu____49103;_},_e0::e1::e2::[])
          when
          (((let uu____49115 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49115 = "FStar.Buffer.rcreate_mm") ||
              (let uu____49120 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____49120 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____49125 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____49125 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____49130 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49130 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____49134 =
            let uu____49141 = translate_expr env e1  in
            let uu____49142 = translate_expr env e2  in
            (ManuallyManaged, uu____49141, uu____49142)  in
          EBufCreate uu____49134
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49144;
                  FStar_Extraction_ML_Syntax.loc = uu____49145;_},uu____49146);
             FStar_Extraction_ML_Syntax.mlty = uu____49147;
             FStar_Extraction_ML_Syntax.loc = uu____49148;_},_erid::elen::[])
          when
          let uu____49157 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49157 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____49161 =
            let uu____49166 = translate_expr env elen  in
            (ManuallyManaged, uu____49166)  in
          EBufCreateNoInit uu____49161
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49168;
                  FStar_Extraction_ML_Syntax.loc = uu____49169;_},uu____49170);
             FStar_Extraction_ML_Syntax.mlty = uu____49171;
             FStar_Extraction_ML_Syntax.loc = uu____49172;_},e2::[])
          when
          let uu____49180 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49180 = "FStar.HyperStack.ST.rfree" ->
          let uu____49184 = translate_expr env e2  in EBufFree uu____49184
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49186;
                  FStar_Extraction_ML_Syntax.loc = uu____49187;_},uu____49188);
             FStar_Extraction_ML_Syntax.mlty = uu____49189;
             FStar_Extraction_ML_Syntax.loc = uu____49190;_},e2::[])
          when
          (let uu____49200 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____49200 = "FStar.Buffer.rfree") ||
            (let uu____49205 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49205 = "LowStar.Monotonic.Buffer.free")
          -> let uu____49209 = translate_expr env e2  in EBufFree uu____49209
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49211;
                  FStar_Extraction_ML_Syntax.loc = uu____49212;_},uu____49213);
             FStar_Extraction_ML_Syntax.mlty = uu____49214;
             FStar_Extraction_ML_Syntax.loc = uu____49215;_},e1::e2::_e3::[])
          when
          let uu____49225 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49225 = "FStar.Buffer.sub" ->
          let uu____49229 =
            let uu____49234 = translate_expr env e1  in
            let uu____49235 = translate_expr env e2  in
            (uu____49234, uu____49235)  in
          EBufSub uu____49229
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49237;
                  FStar_Extraction_ML_Syntax.loc = uu____49238;_},uu____49239);
             FStar_Extraction_ML_Syntax.mlty = uu____49240;
             FStar_Extraction_ML_Syntax.loc = uu____49241;_},e1::e2::_e3::[])
          when
          let uu____49251 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49251 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____49255 =
            let uu____49260 = translate_expr env e1  in
            let uu____49261 = translate_expr env e2  in
            (uu____49260, uu____49261)  in
          EBufSub uu____49255
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49263;
                  FStar_Extraction_ML_Syntax.loc = uu____49264;_},uu____49265);
             FStar_Extraction_ML_Syntax.mlty = uu____49266;
             FStar_Extraction_ML_Syntax.loc = uu____49267;_},e1::e2::[])
          when
          let uu____49276 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49276 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49281;
                  FStar_Extraction_ML_Syntax.loc = uu____49282;_},uu____49283);
             FStar_Extraction_ML_Syntax.mlty = uu____49284;
             FStar_Extraction_ML_Syntax.loc = uu____49285;_},e1::e2::[])
          when
          let uu____49294 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49294 = "FStar.Buffer.offset" ->
          let uu____49298 =
            let uu____49303 = translate_expr env e1  in
            let uu____49304 = translate_expr env e2  in
            (uu____49303, uu____49304)  in
          EBufSub uu____49298
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49306;
                  FStar_Extraction_ML_Syntax.loc = uu____49307;_},uu____49308);
             FStar_Extraction_ML_Syntax.mlty = uu____49309;
             FStar_Extraction_ML_Syntax.loc = uu____49310;_},e1::e2::[])
          when
          let uu____49319 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49319 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____49323 =
            let uu____49328 = translate_expr env e1  in
            let uu____49329 = translate_expr env e2  in
            (uu____49328, uu____49329)  in
          EBufSub uu____49323
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49331;
                  FStar_Extraction_ML_Syntax.loc = uu____49332;_},uu____49333);
             FStar_Extraction_ML_Syntax.mlty = uu____49334;
             FStar_Extraction_ML_Syntax.loc = uu____49335;_},e1::e2::e3::[])
          when
          (((let uu____49347 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49347 = "FStar.Buffer.upd") ||
              (let uu____49352 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____49352 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____49357 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____49357 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____49362 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49362 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____49366 =
            let uu____49373 = translate_expr env e1  in
            let uu____49374 = translate_expr env e2  in
            let uu____49375 = translate_expr env e3  in
            (uu____49373, uu____49374, uu____49375)  in
          EBufWrite uu____49366
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49377;
                  FStar_Extraction_ML_Syntax.loc = uu____49378;_},uu____49379);
             FStar_Extraction_ML_Syntax.mlty = uu____49380;
             FStar_Extraction_ML_Syntax.loc = uu____49381;_},e1::e2::[])
          when
          let uu____49390 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49390 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____49394 =
            let uu____49401 = translate_expr env e1  in
            let uu____49402 = translate_expr env e2  in
            (uu____49401, (EConstant (UInt32, "0")), uu____49402)  in
          EBufWrite uu____49394
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____49406;
             FStar_Extraction_ML_Syntax.loc = uu____49407;_},uu____49408::[])
          when
          let uu____49411 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49411 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____49416;
             FStar_Extraction_ML_Syntax.loc = uu____49417;_},uu____49418::[])
          when
          let uu____49421 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49421 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49426;
                  FStar_Extraction_ML_Syntax.loc = uu____49427;_},uu____49428);
             FStar_Extraction_ML_Syntax.mlty = uu____49429;
             FStar_Extraction_ML_Syntax.loc = uu____49430;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____49444 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____49444 = "FStar.Buffer.blit") ||
             (let uu____49449 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____49449 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____49454 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49454 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____49458 =
            let uu____49469 = translate_expr env e1  in
            let uu____49470 = translate_expr env e2  in
            let uu____49471 = translate_expr env e3  in
            let uu____49472 = translate_expr env e4  in
            let uu____49473 = translate_expr env e5  in
            (uu____49469, uu____49470, uu____49471, uu____49472, uu____49473)
             in
          EBufBlit uu____49458
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49475;
                  FStar_Extraction_ML_Syntax.loc = uu____49476;_},uu____49477);
             FStar_Extraction_ML_Syntax.mlty = uu____49478;
             FStar_Extraction_ML_Syntax.loc = uu____49479;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____49495 =
            let uu____49502 = translate_expr env e1  in
            let uu____49503 = translate_expr env e2  in
            let uu____49504 = translate_expr env e3  in
            (uu____49502, uu____49503, uu____49504)  in
          EBufFill uu____49495
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____49506;
             FStar_Extraction_ML_Syntax.loc = uu____49507;_},uu____49508::[])
          when
          let uu____49511 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49511 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____49516;
                  FStar_Extraction_ML_Syntax.loc = uu____49517;_},uu____49518);
             FStar_Extraction_ML_Syntax.mlty = uu____49519;
             FStar_Extraction_ML_Syntax.loc = uu____49520;_},_ebuf::_eseq::[])
          when
          (((let uu____49531 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49531 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____49536 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____49536 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____49541 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____49541 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____49546 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____49546 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____49551;
             FStar_Extraction_ML_Syntax.loc = uu____49552;_},e1::[])
          when
          let uu____49556 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____49556 = "Obj.repr" ->
          let uu____49560 =
            let uu____49565 = translate_expr env e1  in (uu____49565, TAny)
             in
          ECast uu____49560
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____49568;
             FStar_Extraction_ML_Syntax.loc = uu____49569;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____49585 = FStar_Util.must (mk_width m)  in
          let uu____49586 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____49585 uu____49586 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____49588;
             FStar_Extraction_ML_Syntax.loc = uu____49589;_},args)
          when is_bool_op op ->
          let uu____49603 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____49603 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____49605;
             FStar_Extraction_ML_Syntax.loc = uu____49606;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49608;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49609;_}::[])
          when is_machine_int m ->
          let uu____49634 =
            let uu____49640 = FStar_Util.must (mk_width m)  in
            (uu____49640, c)  in
          EConstant uu____49634
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____49643;
             FStar_Extraction_ML_Syntax.loc = uu____49644;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49646;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49647;_}::[])
          when is_machine_int m ->
          let uu____49672 =
            let uu____49678 = FStar_Util.must (mk_width m)  in
            (uu____49678, c)  in
          EConstant uu____49672
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49680;
             FStar_Extraction_ML_Syntax.loc = uu____49681;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49683;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49684;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____49697 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49699;
             FStar_Extraction_ML_Syntax.loc = uu____49700;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49702;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49703;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____49720 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49722;
             FStar_Extraction_ML_Syntax.loc = uu____49723;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49725;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49726;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____49741 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49743;
             FStar_Extraction_ML_Syntax.loc = uu____49744;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49746;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49747;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____49762 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____49765;
             FStar_Extraction_ML_Syntax.loc = uu____49766;_},arg::[])
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
            let uu____49794 =
              let uu____49799 = translate_expr env arg  in
              (uu____49799, (TInt UInt64))  in
            ECast uu____49794
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____49804 =
                 let uu____49809 = translate_expr env arg  in
                 (uu____49809, (TInt UInt32))  in
               ECast uu____49804)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____49814 =
                   let uu____49819 = translate_expr env arg  in
                   (uu____49819, (TInt UInt16))  in
                 ECast uu____49814)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____49824 =
                     let uu____49829 = translate_expr env arg  in
                     (uu____49829, (TInt UInt8))  in
                   ECast uu____49824)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____49834 =
                       let uu____49839 = translate_expr env arg  in
                       (uu____49839, (TInt Int64))  in
                     ECast uu____49834)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____49844 =
                         let uu____49849 = translate_expr env arg  in
                         (uu____49849, (TInt Int32))  in
                       ECast uu____49844)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____49854 =
                           let uu____49859 = translate_expr env arg  in
                           (uu____49859, (TInt Int16))  in
                         ECast uu____49854)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____49864 =
                             let uu____49869 = translate_expr env arg  in
                             (uu____49869, (TInt Int8))  in
                           ECast uu____49864)
                        else
                          (let uu____49872 =
                             let uu____49879 =
                               let uu____49882 = translate_expr env arg  in
                               [uu____49882]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____49879)
                              in
                           EApp uu____49872)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____49902 =
            let uu____49909 = translate_expr env head1  in
            let uu____49910 = FStar_List.map (translate_expr env) args  in
            (uu____49909, uu____49910)  in
          EApp uu____49902
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____49921 =
            let uu____49928 = translate_expr env head1  in
            let uu____49929 = FStar_List.map (translate_type env) ty_args  in
            (uu____49928, uu____49929)  in
          ETypApp uu____49921
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____49937 =
            let uu____49942 = translate_expr env e1  in
            let uu____49943 = translate_type env t_to  in
            (uu____49942, uu____49943)  in
          ECast uu____49937
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____49944,fields) ->
          let uu____49966 =
            let uu____49978 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____49979 =
              FStar_List.map
                (fun uu____50001  ->
                   match uu____50001 with
                   | (field,expr) ->
                       let uu____50016 = translate_expr env expr  in
                       (field, uu____50016)) fields
               in
            (uu____49978, uu____49979)  in
          EFlat uu____49966
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____50027 =
            let uu____50035 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____50036 = translate_expr env e1  in
            (uu____50035, uu____50036, (FStar_Pervasives_Native.snd path))
             in
          EField uu____50027
      | FStar_Extraction_ML_Syntax.MLE_Let uu____50042 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____50055) ->
          let uu____50060 =
            let uu____50062 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____50062
             in
          failwith uu____50060
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____50074 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____50074
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____50080 = FStar_List.map (translate_expr env) es  in
          ETuple uu____50080
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____50083,cons1),es) ->
          let uu____50098 =
            let uu____50108 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____50109 = FStar_List.map (translate_expr env) es  in
            (uu____50108, cons1, uu____50109)  in
          ECons uu____50098
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____50135 =
            let uu____50144 = translate_expr env1 body  in
            let uu____50145 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____50144, uu____50145)  in
          EFun uu____50135
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____50155 =
            let uu____50162 = translate_expr env e1  in
            let uu____50163 = translate_expr env e2  in
            let uu____50164 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____50162, uu____50163, uu____50164)  in
          EIfThenElse uu____50155
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____50166 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____50174 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____50190 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____50208 =
              let uu____50223 = FStar_List.map (translate_type env) ts  in
              (lid, uu____50223)  in
            TApp uu____50208
          else TQualified lid
      | uu____50238 -> failwith "invalid argument: assert_lid"

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
    fun uu____50265  ->
      match uu____50265 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____50292 = translate_pat env pat  in
            (match uu____50292 with
             | (env1,pat1) ->
                 let uu____50303 = translate_expr env1 expr  in
                 (pat1, uu____50303))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_50311  ->
    match uu___420_50311 with
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
          let uu____50378 =
            let uu____50379 =
              let uu____50385 = translate_width sw  in (uu____50385, s)  in
            PConstant uu____50379  in
          (env, uu____50378)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____50395,cons1),ps) ->
          let uu____50410 =
            FStar_List.fold_left
              (fun uu____50430  ->
                 fun p1  ->
                   match uu____50430 with
                   | (env1,acc) ->
                       let uu____50450 = translate_pat env1 p1  in
                       (match uu____50450 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____50410 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____50480,ps) ->
          let uu____50502 =
            FStar_List.fold_left
              (fun uu____50539  ->
                 fun uu____50540  ->
                   match (uu____50539, uu____50540) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____50620 = translate_pat env1 p1  in
                       (match uu____50620 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____50502 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____50691 =
            FStar_List.fold_left
              (fun uu____50711  ->
                 fun p1  ->
                   match uu____50711 with
                   | (env1,acc) ->
                       let uu____50731 = translate_pat env1 p1  in
                       (match uu____50731 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____50691 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____50758 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____50764 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____50778 =
            let uu____50780 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____50780
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____50778
          then
            let uu____50795 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____50795
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____50822) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____50840 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____50842 ->
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
          let uu____50866 =
            let uu____50873 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____50873)  in
          EApp uu____50866
