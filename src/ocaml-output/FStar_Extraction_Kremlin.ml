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
    match projectee with | DGlobal _0 -> true | uu____46574 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____46686 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____46812 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____46920 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____47053 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____47171 -> false
  
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
    | uu____47313 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____47356 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____47367 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____47378 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____47389 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____47400 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____47411 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____47422 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____47433 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____47446 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____47468 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____47481 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____47505 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____47529 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____47551 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____47562 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____47573 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____47584 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____47597 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____47628 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____47677 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____47711 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____47729 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____47773 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____47817 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____47861 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____47901 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____47931 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____47969 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____48011 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____48049 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____48091 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____48133 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____48193 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____48247 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____48283 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____48314 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____48325 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____48338 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____48360 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____48371 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____48383 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____48414 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____48474 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____48519 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____48557 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____48597 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____48632 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____48685 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____48724 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____48755 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____48800 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____48823 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____48847 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____48878 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____48889 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____48900 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____48911 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____48922 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____48933 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____48944 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____48955 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____48966 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____48977 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____48988 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____48999 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____49010 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____49021 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____49032 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____49043 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____49054 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____49065 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____49076 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____49087 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____49098 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____49109 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____49120 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____49131 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____49142 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____49153 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____49166 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____49189 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____49216 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____49259 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____49292 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____49338 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____49372 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____49383 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____49394 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____49405 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____49416 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____49427 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____49438 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____49449 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____49460 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____49471 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____49520 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____49540 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____49559 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____49579 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____49622 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____49633 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____49649 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____49682 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____49719 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____49783 -> false
  
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
  'Auu____49886 'Auu____49887 'Auu____49888 .
    ('Auu____49886 * 'Auu____49887 * 'Auu____49888) -> 'Auu____49886
  =
  fun uu____49899  ->
    match uu____49899 with | (x,uu____49907,uu____49908) -> x
  
let snd3 :
  'Auu____49918 'Auu____49919 'Auu____49920 .
    ('Auu____49918 * 'Auu____49919 * 'Auu____49920) -> 'Auu____49919
  =
  fun uu____49931  ->
    match uu____49931 with | (uu____49938,x,uu____49940) -> x
  
let thd3 :
  'Auu____49950 'Auu____49951 'Auu____49952 .
    ('Auu____49950 * 'Auu____49951 * 'Auu____49952) -> 'Auu____49952
  =
  fun uu____49963  ->
    match uu____49963 with | (uu____49970,uu____49971,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_49981  ->
    match uu___413_49981 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____49993 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_50003  ->
    match uu___414_50003 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____50012 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_50033  ->
    match uu___415_50033 with
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
    | uu____50078 -> FStar_Pervasives_Native.None
  
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
      let uu___575_50234 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_50234.names_t);
        module_name = (uu___575_50234.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_50248 = env  in
      {
        names = (uu___579_50248.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_50248.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____50263 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____50263 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_50287  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_50294 ->
          let uu____50296 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50296
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_50316  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_50325 ->
          let uu____50327 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50327
  
let add_binders :
  'Auu____50338 . env -> (Prims.string * 'Auu____50338) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____50373  ->
             match uu____50373 with | (name,uu____50380) -> extend env1 name)
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
      | uu____50432 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____50651  ->
    match uu____50651 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____50700 = m  in
               match uu____50700 with
               | (path,uu____50715,uu____50716) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_50734  ->
                  match () with
                  | () ->
                      ((let uu____50738 =
                          let uu____50740 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____50740  in
                        if uu____50738
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____50746 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____50746))) ()
             with
             | e ->
                 ((let uu____50755 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____50755);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____50758  ->
    match uu____50758 with
    | (module_name,modul,uu____50773) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____50808 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_50822  ->
         match uu___416_50822 with
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
         | uu____50833 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____50837 =
      FStar_List.choose
        (fun uu___417_50844  ->
           match uu___417_50844 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____50851 -> FStar_Pervasives_Native.None) flags
       in
    match uu____50837 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____50864 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____50878 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____50880 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____50885) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50912;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____50915;_} when
            FStar_Util.for_some
              (fun uu___418_50920  ->
                 match uu___418_50920 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____50923 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____50944 =
                let uu____50945 =
                  let uu____50966 = translate_cc meta  in
                  let uu____50969 = translate_flags meta  in
                  let uu____50972 = translate_type env t0  in
                  (uu____50966, uu____50969, name1, uu____50972)  in
                DExternal uu____50945  in
              FStar_Pervasives_Native.Some uu____50944
            else
              ((let uu____50988 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____50988);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50994;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____50997;
                FStar_Extraction_ML_Syntax.loc = uu____50998;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51000;_} ->
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
               let rec find_return_type eff i uu___419_51057 =
                 match uu___419_51057 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____51066,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____51086 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____51086 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____51112 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____51112
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____51130) ->
                           let uu____51131 = translate_flags meta  in
                           MustDisappear :: uu____51131
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____51134 = translate_flags meta  in
                           MustDisappear :: uu____51134
                       | uu____51137 -> translate_flags meta  in
                     try
                       (fun uu___779_51146  ->
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
                         ((let uu____51178 =
                             let uu____51184 =
                               let uu____51186 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____51186 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____51184)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____51178);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51212;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51215;_} ->
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
                 (fun uu___806_51252  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____51276 =
                       let uu____51282 =
                         let uu____51284 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____51286 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____51284 uu____51286
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____51282)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____51276);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51304;
            FStar_Extraction_ML_Syntax.mllb_def = uu____51305;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____51306;
            FStar_Extraction_ML_Syntax.print_typ = uu____51307;_} ->
            ((let uu____51314 =
                let uu____51320 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____51320)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____51314);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____51327 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____51327
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____51341 = ty  in
      match uu____51341 with
      | (uu____51344,uu____51345,uu____51346,uu____51347,flags,uu____51349)
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
                     (let uu____51423 =
                        let uu____51424 =
                          let uu____51444 = translate_flags flags1  in
                          let uu____51447 = translate_type env1 t  in
                          (name1, uu____51444, (FStar_List.length args),
                            uu____51447)
                           in
                        DTypeAlias uu____51424  in
                      FStar_Pervasives_Native.Some uu____51423)
             | (uu____51460,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____51505 =
                   let uu____51506 =
                     let uu____51538 = translate_flags flags1  in
                     let uu____51541 =
                       FStar_List.map
                         (fun uu____51573  ->
                            match uu____51573 with
                            | (f,t) ->
                                let uu____51593 =
                                  let uu____51599 = translate_type env1 t  in
                                  (uu____51599, false)  in
                                (f, uu____51593)) fields
                        in
                     (name1, uu____51538, (FStar_List.length args),
                       uu____51541)
                      in
                   DTypeFlat uu____51506  in
                 FStar_Pervasives_Native.Some uu____51505
             | (uu____51632,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____51682 =
                   let uu____51683 =
                     let uu____51722 =
                       FStar_List.map
                         (fun uu____51775  ->
                            match uu____51775 with
                            | (cons1,ts) ->
                                let uu____51823 =
                                  FStar_List.map
                                    (fun uu____51855  ->
                                       match uu____51855 with
                                       | (name2,t) ->
                                           let uu____51875 =
                                             let uu____51881 =
                                               translate_type env1 t  in
                                             (uu____51881, false)  in
                                           (name2, uu____51875)) ts
                                   in
                                (cons1, uu____51823)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____51722)
                      in
                   DTypeVariant uu____51683  in
                 FStar_Pervasives_Native.Some uu____51682
             | (uu____51934,name,_mangled_name,uu____51937,uu____51938,uu____51939)
                 ->
                 ((let uu____51955 =
                     let uu____51961 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____51961)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____51955);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____51969 = find_t env name  in TBound uu____51969
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____51972,t2) ->
          let uu____51974 =
            let uu____51979 = translate_type env t1  in
            let uu____51980 = translate_type env t2  in
            (uu____51979, uu____51980)  in
          TArrow uu____51974
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____51984 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____51984 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____51991 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____51991 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____52008 = FStar_Util.must (mk_width m)  in TInt uu____52008
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____52022 = FStar_Util.must (mk_width m)  in TInt uu____52022
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____52027 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52027 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____52031::arg::uu____52033::[],p) when
          (((let uu____52039 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52039 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____52044 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52044 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____52049 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52049 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____52054 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52054 = "FStar.HyperStack.ST.s_mref")
          -> let uu____52058 = translate_type env arg  in TBuf uu____52058
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____52060::[],p) when
          ((((((((((let uu____52066 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52066 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____52071 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52071 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____52076 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52076 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____52081 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52081 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____52086 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52086 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____52091 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52091 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____52096 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52096 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____52101 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52101 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____52106 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52106 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____52111 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52111 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____52116 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52116 = "FStar.HyperStack.ST.mmmref")
          -> let uu____52120 = translate_type env arg  in TBuf uu____52120
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____52122::uu____52123::[],p) when
          let uu____52127 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52127 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____52131 = translate_type env arg  in TBuf uu____52131
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____52138 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52138 = "FStar.Buffer.buffer") ||
                        (let uu____52143 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____52143 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____52148 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____52148 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____52153 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52153 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____52158 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52158 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____52163 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52163 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____52168 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52168 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____52173 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52173 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____52178 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52178 = "FStar.HyperStack.mmref"))
                ||
                (let uu____52183 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52183 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____52188 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52188 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____52193 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52193 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____52198 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52198 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____52203 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52203 = "FStar.HyperStack.ST.mmref")
          -> let uu____52207 = translate_type env arg  in TBuf uu____52207
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52208::arg::[],p) when
          (let uu____52215 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52215 = "FStar.HyperStack.s_ref") ||
            (let uu____52220 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52220 = "FStar.HyperStack.ST.s_ref")
          -> let uu____52224 = translate_type env arg  in TBuf uu____52224
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52225::[],p) when
          let uu____52229 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52229 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____52281 = FStar_List.map (translate_type env) args  in
          TTuple uu____52281
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____52292 =
              let uu____52307 = FStar_List.map (translate_type env) args  in
              (lid, uu____52307)  in
            TApp uu____52292
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____52325 = FStar_List.map (translate_type env) ts  in
          TTuple uu____52325

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
    fun uu____52343  ->
      match uu____52343 with
      | (name,typ) ->
          let uu____52353 = translate_type env typ  in
          { name; typ = uu____52353; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____52360 = find env name  in EBound uu____52360
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____52374 =
            let uu____52379 = FStar_Util.must (mk_op op)  in
            let uu____52380 = FStar_Util.must (mk_width m)  in
            (uu____52379, uu____52380)  in
          EOp uu____52374
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____52390 =
            let uu____52395 = FStar_Util.must (mk_bool_op op)  in
            (uu____52395, Bool)  in
          EOp uu____52390
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
            let uu____52418 = translate_type env typ  in
            { name; typ = uu____52418; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____52445 =
            let uu____52456 = translate_expr env expr  in
            let uu____52457 = translate_branches env branches  in
            (uu____52456, uu____52457)  in
          EMatch uu____52445
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52471;
                  FStar_Extraction_ML_Syntax.loc = uu____52472;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____52474;
             FStar_Extraction_ML_Syntax.loc = uu____52475;_},arg::[])
          when
          let uu____52481 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52481 = "FStar.Dyn.undyn" ->
          let uu____52485 =
            let uu____52490 = translate_expr env arg  in
            let uu____52491 = translate_type env t  in
            (uu____52490, uu____52491)  in
          ECast uu____52485
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52493;
                  FStar_Extraction_ML_Syntax.loc = uu____52494;_},uu____52495);
             FStar_Extraction_ML_Syntax.mlty = uu____52496;
             FStar_Extraction_ML_Syntax.loc = uu____52497;_},uu____52498)
          when
          let uu____52507 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52507 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52512;
                  FStar_Extraction_ML_Syntax.loc = uu____52513;_},uu____52514);
             FStar_Extraction_ML_Syntax.mlty = uu____52515;
             FStar_Extraction_ML_Syntax.loc = uu____52516;_},arg::[])
          when
          ((let uu____52526 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52526 = "FStar.HyperStack.All.failwith") ||
             (let uu____52531 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52531 = "FStar.Error.unexpected"))
            ||
            (let uu____52536 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52536 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____52541;
               FStar_Extraction_ML_Syntax.loc = uu____52542;_} -> EAbortS msg
           | uu____52544 ->
               let print7 =
                 let uu____52546 =
                   let uu____52547 =
                     let uu____52548 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____52548
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____52547  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____52546
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
                  FStar_Extraction_ML_Syntax.mlty = uu____52555;
                  FStar_Extraction_ML_Syntax.loc = uu____52556;_},uu____52557);
             FStar_Extraction_ML_Syntax.mlty = uu____52558;
             FStar_Extraction_ML_Syntax.loc = uu____52559;_},e1::[])
          when
          (let uu____52569 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52569 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____52574 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52574 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52579;
                  FStar_Extraction_ML_Syntax.loc = uu____52580;_},uu____52581);
             FStar_Extraction_ML_Syntax.mlty = uu____52582;
             FStar_Extraction_ML_Syntax.loc = uu____52583;_},e1::e2::[])
          when
          (((let uu____52594 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52594 = "FStar.Buffer.index") ||
              (let uu____52599 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52599 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____52604 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52604 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____52609 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52609 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____52613 =
            let uu____52618 = translate_expr env e1  in
            let uu____52619 = translate_expr env e2  in
            (uu____52618, uu____52619)  in
          EBufRead uu____52613
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52621;
                  FStar_Extraction_ML_Syntax.loc = uu____52622;_},uu____52623);
             FStar_Extraction_ML_Syntax.mlty = uu____52624;
             FStar_Extraction_ML_Syntax.loc = uu____52625;_},e1::[])
          when
          let uu____52633 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52633 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____52637 =
            let uu____52642 = translate_expr env e1  in
            (uu____52642, (EConstant (UInt32, "0")))  in
          EBufRead uu____52637
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52646;
                  FStar_Extraction_ML_Syntax.loc = uu____52647;_},uu____52648);
             FStar_Extraction_ML_Syntax.mlty = uu____52649;
             FStar_Extraction_ML_Syntax.loc = uu____52650;_},e1::e2::[])
          when
          ((let uu____52661 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52661 = "FStar.Buffer.create") ||
             (let uu____52666 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52666 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____52671 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52671 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____52675 =
            let uu____52682 = translate_expr env e1  in
            let uu____52683 = translate_expr env e2  in
            (Stack, uu____52682, uu____52683)  in
          EBufCreate uu____52675
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52685;
                  FStar_Extraction_ML_Syntax.loc = uu____52686;_},uu____52687);
             FStar_Extraction_ML_Syntax.mlty = uu____52688;
             FStar_Extraction_ML_Syntax.loc = uu____52689;_},elen::[])
          when
          let uu____52697 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52697 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____52701 =
            let uu____52706 = translate_expr env elen  in
            (Stack, uu____52706)  in
          EBufCreateNoInit uu____52701
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52708;
                  FStar_Extraction_ML_Syntax.loc = uu____52709;_},uu____52710);
             FStar_Extraction_ML_Syntax.mlty = uu____52711;
             FStar_Extraction_ML_Syntax.loc = uu____52712;_},init1::[])
          when
          let uu____52720 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52720 = "FStar.HyperStack.ST.salloc" ->
          let uu____52724 =
            let uu____52731 = translate_expr env init1  in
            (Stack, uu____52731, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52724
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52735;
                  FStar_Extraction_ML_Syntax.loc = uu____52736;_},uu____52737);
             FStar_Extraction_ML_Syntax.mlty = uu____52738;
             FStar_Extraction_ML_Syntax.loc = uu____52739;_},e2::[])
          when
          ((let uu____52749 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52749 = "FStar.Buffer.createL") ||
             (let uu____52754 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52754 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____52759 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52759 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____52763 =
            let uu____52770 =
              let uu____52773 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52773  in
            (Stack, uu____52770)  in
          EBufCreateL uu____52763
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52779;
                  FStar_Extraction_ML_Syntax.loc = uu____52780;_},uu____52781);
             FStar_Extraction_ML_Syntax.mlty = uu____52782;
             FStar_Extraction_ML_Syntax.loc = uu____52783;_},_erid::e2::[])
          when
          (let uu____52794 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52794 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____52799 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52799 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____52803 =
            let uu____52810 =
              let uu____52813 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52813  in
            (Eternal, uu____52810)  in
          EBufCreateL uu____52803
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52819;
                  FStar_Extraction_ML_Syntax.loc = uu____52820;_},uu____52821);
             FStar_Extraction_ML_Syntax.mlty = uu____52822;
             FStar_Extraction_ML_Syntax.loc = uu____52823;_},_rid::init1::[])
          when
          let uu____52832 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52832 = "FStar.HyperStack.ST.ralloc" ->
          let uu____52836 =
            let uu____52843 = translate_expr env init1  in
            (Eternal, uu____52843, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52836
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52847;
                  FStar_Extraction_ML_Syntax.loc = uu____52848;_},uu____52849);
             FStar_Extraction_ML_Syntax.mlty = uu____52850;
             FStar_Extraction_ML_Syntax.loc = uu____52851;_},_e0::e1::e2::[])
          when
          ((let uu____52863 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52863 = "FStar.Buffer.rcreate") ||
             (let uu____52868 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52868 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____52873 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52873 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____52877 =
            let uu____52884 = translate_expr env e1  in
            let uu____52885 = translate_expr env e2  in
            (Eternal, uu____52884, uu____52885)  in
          EBufCreate uu____52877
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52887;
                  FStar_Extraction_ML_Syntax.loc = uu____52888;_},uu____52889);
             FStar_Extraction_ML_Syntax.mlty = uu____52890;
             FStar_Extraction_ML_Syntax.loc = uu____52891;_},_erid::elen::[])
          when
          let uu____52900 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52900 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____52904 =
            let uu____52909 = translate_expr env elen  in
            (Eternal, uu____52909)  in
          EBufCreateNoInit uu____52904
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52911;
                  FStar_Extraction_ML_Syntax.loc = uu____52912;_},uu____52913);
             FStar_Extraction_ML_Syntax.mlty = uu____52914;
             FStar_Extraction_ML_Syntax.loc = uu____52915;_},_rid::init1::[])
          when
          let uu____52924 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52924 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____52928 =
            let uu____52935 = translate_expr env init1  in
            (ManuallyManaged, uu____52935, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52928
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52939;
                  FStar_Extraction_ML_Syntax.loc = uu____52940;_},uu____52941);
             FStar_Extraction_ML_Syntax.mlty = uu____52942;
             FStar_Extraction_ML_Syntax.loc = uu____52943;_},_e0::e1::e2::[])
          when
          (((let uu____52955 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52955 = "FStar.Buffer.rcreate_mm") ||
              (let uu____52960 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52960 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____52965 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52965 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____52970 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52970 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____52974 =
            let uu____52981 = translate_expr env e1  in
            let uu____52982 = translate_expr env e2  in
            (ManuallyManaged, uu____52981, uu____52982)  in
          EBufCreate uu____52974
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52984;
                  FStar_Extraction_ML_Syntax.loc = uu____52985;_},uu____52986);
             FStar_Extraction_ML_Syntax.mlty = uu____52987;
             FStar_Extraction_ML_Syntax.loc = uu____52988;_},_erid::elen::[])
          when
          let uu____52997 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52997 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____53001 =
            let uu____53006 = translate_expr env elen  in
            (ManuallyManaged, uu____53006)  in
          EBufCreateNoInit uu____53001
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53008;
                  FStar_Extraction_ML_Syntax.loc = uu____53009;_},uu____53010);
             FStar_Extraction_ML_Syntax.mlty = uu____53011;
             FStar_Extraction_ML_Syntax.loc = uu____53012;_},e2::[])
          when
          let uu____53020 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53020 = "FStar.HyperStack.ST.rfree" ->
          let uu____53024 = translate_expr env e2  in EBufFree uu____53024
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53026;
                  FStar_Extraction_ML_Syntax.loc = uu____53027;_},uu____53028);
             FStar_Extraction_ML_Syntax.mlty = uu____53029;
             FStar_Extraction_ML_Syntax.loc = uu____53030;_},e2::[])
          when
          (let uu____53040 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____53040 = "FStar.Buffer.rfree") ||
            (let uu____53045 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53045 = "LowStar.Monotonic.Buffer.free")
          -> let uu____53049 = translate_expr env e2  in EBufFree uu____53049
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53051;
                  FStar_Extraction_ML_Syntax.loc = uu____53052;_},uu____53053);
             FStar_Extraction_ML_Syntax.mlty = uu____53054;
             FStar_Extraction_ML_Syntax.loc = uu____53055;_},e1::e2::_e3::[])
          when
          let uu____53065 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53065 = "FStar.Buffer.sub" ->
          let uu____53069 =
            let uu____53074 = translate_expr env e1  in
            let uu____53075 = translate_expr env e2  in
            (uu____53074, uu____53075)  in
          EBufSub uu____53069
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53077;
                  FStar_Extraction_ML_Syntax.loc = uu____53078;_},uu____53079);
             FStar_Extraction_ML_Syntax.mlty = uu____53080;
             FStar_Extraction_ML_Syntax.loc = uu____53081;_},e1::e2::_e3::[])
          when
          let uu____53091 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53091 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____53095 =
            let uu____53100 = translate_expr env e1  in
            let uu____53101 = translate_expr env e2  in
            (uu____53100, uu____53101)  in
          EBufSub uu____53095
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53103;
                  FStar_Extraction_ML_Syntax.loc = uu____53104;_},uu____53105);
             FStar_Extraction_ML_Syntax.mlty = uu____53106;
             FStar_Extraction_ML_Syntax.loc = uu____53107;_},e1::e2::[])
          when
          let uu____53116 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53116 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53121;
                  FStar_Extraction_ML_Syntax.loc = uu____53122;_},uu____53123);
             FStar_Extraction_ML_Syntax.mlty = uu____53124;
             FStar_Extraction_ML_Syntax.loc = uu____53125;_},e1::e2::[])
          when
          let uu____53134 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53134 = "FStar.Buffer.offset" ->
          let uu____53138 =
            let uu____53143 = translate_expr env e1  in
            let uu____53144 = translate_expr env e2  in
            (uu____53143, uu____53144)  in
          EBufSub uu____53138
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53146;
                  FStar_Extraction_ML_Syntax.loc = uu____53147;_},uu____53148);
             FStar_Extraction_ML_Syntax.mlty = uu____53149;
             FStar_Extraction_ML_Syntax.loc = uu____53150;_},e1::e2::[])
          when
          let uu____53159 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53159 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____53163 =
            let uu____53168 = translate_expr env e1  in
            let uu____53169 = translate_expr env e2  in
            (uu____53168, uu____53169)  in
          EBufSub uu____53163
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53171;
                  FStar_Extraction_ML_Syntax.loc = uu____53172;_},uu____53173);
             FStar_Extraction_ML_Syntax.mlty = uu____53174;
             FStar_Extraction_ML_Syntax.loc = uu____53175;_},e1::e2::e3::[])
          when
          (((let uu____53187 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53187 = "FStar.Buffer.upd") ||
              (let uu____53192 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53192 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____53197 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53197 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____53202 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53202 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____53206 =
            let uu____53213 = translate_expr env e1  in
            let uu____53214 = translate_expr env e2  in
            let uu____53215 = translate_expr env e3  in
            (uu____53213, uu____53214, uu____53215)  in
          EBufWrite uu____53206
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53217;
                  FStar_Extraction_ML_Syntax.loc = uu____53218;_},uu____53219);
             FStar_Extraction_ML_Syntax.mlty = uu____53220;
             FStar_Extraction_ML_Syntax.loc = uu____53221;_},e1::e2::[])
          when
          let uu____53230 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53230 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____53234 =
            let uu____53241 = translate_expr env e1  in
            let uu____53242 = translate_expr env e2  in
            (uu____53241, (EConstant (UInt32, "0")), uu____53242)  in
          EBufWrite uu____53234
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53246;
             FStar_Extraction_ML_Syntax.loc = uu____53247;_},uu____53248::[])
          when
          let uu____53251 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53251 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53256;
             FStar_Extraction_ML_Syntax.loc = uu____53257;_},uu____53258::[])
          when
          let uu____53261 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53261 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53266;
                  FStar_Extraction_ML_Syntax.loc = uu____53267;_},uu____53268);
             FStar_Extraction_ML_Syntax.mlty = uu____53269;
             FStar_Extraction_ML_Syntax.loc = uu____53270;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____53284 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____53284 = "FStar.Buffer.blit") ||
             (let uu____53289 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53289 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____53294 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53294 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____53298 =
            let uu____53309 = translate_expr env e1  in
            let uu____53310 = translate_expr env e2  in
            let uu____53311 = translate_expr env e3  in
            let uu____53312 = translate_expr env e4  in
            let uu____53313 = translate_expr env e5  in
            (uu____53309, uu____53310, uu____53311, uu____53312, uu____53313)
             in
          EBufBlit uu____53298
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53315;
                  FStar_Extraction_ML_Syntax.loc = uu____53316;_},uu____53317);
             FStar_Extraction_ML_Syntax.mlty = uu____53318;
             FStar_Extraction_ML_Syntax.loc = uu____53319;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____53335 =
            let uu____53342 = translate_expr env e1  in
            let uu____53343 = translate_expr env e2  in
            let uu____53344 = translate_expr env e3  in
            (uu____53342, uu____53343, uu____53344)  in
          EBufFill uu____53335
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53346;
             FStar_Extraction_ML_Syntax.loc = uu____53347;_},uu____53348::[])
          when
          let uu____53351 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53351 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53356;
                  FStar_Extraction_ML_Syntax.loc = uu____53357;_},uu____53358);
             FStar_Extraction_ML_Syntax.mlty = uu____53359;
             FStar_Extraction_ML_Syntax.loc = uu____53360;_},_ebuf::_eseq::[])
          when
          (((let uu____53371 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53371 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____53376 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53376 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____53381 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53381 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____53386 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53386 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53391;
             FStar_Extraction_ML_Syntax.loc = uu____53392;_},e1::[])
          when
          let uu____53396 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53396 = "Obj.repr" ->
          let uu____53400 =
            let uu____53405 = translate_expr env e1  in (uu____53405, TAny)
             in
          ECast uu____53400
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53408;
             FStar_Extraction_ML_Syntax.loc = uu____53409;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____53425 = FStar_Util.must (mk_width m)  in
          let uu____53426 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____53425 uu____53426 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53428;
             FStar_Extraction_ML_Syntax.loc = uu____53429;_},args)
          when is_bool_op op ->
          let uu____53443 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____53443 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53445;
             FStar_Extraction_ML_Syntax.loc = uu____53446;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53448;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53449;_}::[])
          when is_machine_int m ->
          let uu____53474 =
            let uu____53480 = FStar_Util.must (mk_width m)  in
            (uu____53480, c)  in
          EConstant uu____53474
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53483;
             FStar_Extraction_ML_Syntax.loc = uu____53484;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53486;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53487;_}::[])
          when is_machine_int m ->
          let uu____53512 =
            let uu____53518 = FStar_Util.must (mk_width m)  in
            (uu____53518, c)  in
          EConstant uu____53512
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53520;
             FStar_Extraction_ML_Syntax.loc = uu____53521;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53523;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53524;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53537 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53539;
             FStar_Extraction_ML_Syntax.loc = uu____53540;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53542;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53543;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53560 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53562;
             FStar_Extraction_ML_Syntax.loc = uu____53563;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53565;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53566;_}::[])
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
               ("LowStar"::"Literal"::[],"buffer_of_literal");
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
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____53602 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____53605;
             FStar_Extraction_ML_Syntax.loc = uu____53606;_},arg::[])
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
            let uu____53634 =
              let uu____53639 = translate_expr env arg  in
              (uu____53639, (TInt UInt64))  in
            ECast uu____53634
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____53644 =
                 let uu____53649 = translate_expr env arg  in
                 (uu____53649, (TInt UInt32))  in
               ECast uu____53644)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____53654 =
                   let uu____53659 = translate_expr env arg  in
                   (uu____53659, (TInt UInt16))  in
                 ECast uu____53654)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____53664 =
                     let uu____53669 = translate_expr env arg  in
                     (uu____53669, (TInt UInt8))  in
                   ECast uu____53664)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____53674 =
                       let uu____53679 = translate_expr env arg  in
                       (uu____53679, (TInt Int64))  in
                     ECast uu____53674)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____53684 =
                         let uu____53689 = translate_expr env arg  in
                         (uu____53689, (TInt Int32))  in
                       ECast uu____53684)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____53694 =
                           let uu____53699 = translate_expr env arg  in
                           (uu____53699, (TInt Int16))  in
                         ECast uu____53694)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____53704 =
                             let uu____53709 = translate_expr env arg  in
                             (uu____53709, (TInt Int8))  in
                           ECast uu____53704)
                        else
                          (let uu____53712 =
                             let uu____53719 =
                               let uu____53722 = translate_expr env arg  in
                               [uu____53722]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____53719)
                              in
                           EApp uu____53712)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____53742 =
            let uu____53749 = translate_expr env head1  in
            let uu____53750 = FStar_List.map (translate_expr env) args  in
            (uu____53749, uu____53750)  in
          EApp uu____53742
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____53761 =
            let uu____53768 = translate_expr env head1  in
            let uu____53769 = FStar_List.map (translate_type env) ty_args  in
            (uu____53768, uu____53769)  in
          ETypApp uu____53761
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____53777 =
            let uu____53782 = translate_expr env e1  in
            let uu____53783 = translate_type env t_to  in
            (uu____53782, uu____53783)  in
          ECast uu____53777
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____53784,fields) ->
          let uu____53806 =
            let uu____53818 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53819 =
              FStar_List.map
                (fun uu____53841  ->
                   match uu____53841 with
                   | (field,expr) ->
                       let uu____53856 = translate_expr env expr  in
                       (field, uu____53856)) fields
               in
            (uu____53818, uu____53819)  in
          EFlat uu____53806
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____53867 =
            let uu____53875 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53876 = translate_expr env e1  in
            (uu____53875, uu____53876, (FStar_Pervasives_Native.snd path))
             in
          EField uu____53867
      | FStar_Extraction_ML_Syntax.MLE_Let uu____53882 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____53895) ->
          let uu____53900 =
            let uu____53902 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____53902
             in
          failwith uu____53900
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____53914 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____53914
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____53920 = FStar_List.map (translate_expr env) es  in
          ETuple uu____53920
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____53923,cons1),es) ->
          let uu____53938 =
            let uu____53948 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53949 = FStar_List.map (translate_expr env) es  in
            (uu____53948, cons1, uu____53949)  in
          ECons uu____53938
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____53975 =
            let uu____53984 = translate_expr env1 body  in
            let uu____53985 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____53984, uu____53985)  in
          EFun uu____53975
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____53995 =
            let uu____54002 = translate_expr env e1  in
            let uu____54003 = translate_expr env e2  in
            let uu____54004 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____54002, uu____54003, uu____54004)  in
          EIfThenElse uu____53995
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____54006 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____54014 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____54030 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____54048 =
              let uu____54063 = FStar_List.map (translate_type env) ts  in
              (lid, uu____54063)  in
            TApp uu____54048
          else TQualified lid
      | uu____54078 -> failwith "invalid argument: assert_lid"

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
    fun uu____54105  ->
      match uu____54105 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____54132 = translate_pat env pat  in
            (match uu____54132 with
             | (env1,pat1) ->
                 let uu____54143 = translate_expr env1 expr  in
                 (pat1, uu____54143))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_54151  ->
    match uu___420_54151 with
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
          let uu____54218 =
            let uu____54219 =
              let uu____54225 = translate_width sw  in (uu____54225, s)  in
            PConstant uu____54219  in
          (env, uu____54218)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____54235,cons1),ps) ->
          let uu____54250 =
            FStar_List.fold_left
              (fun uu____54270  ->
                 fun p1  ->
                   match uu____54270 with
                   | (env1,acc) ->
                       let uu____54290 = translate_pat env1 p1  in
                       (match uu____54290 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54250 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____54320,ps) ->
          let uu____54342 =
            FStar_List.fold_left
              (fun uu____54379  ->
                 fun uu____54380  ->
                   match (uu____54379, uu____54380) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____54460 = translate_pat env1 p1  in
                       (match uu____54460 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____54342 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____54531 =
            FStar_List.fold_left
              (fun uu____54551  ->
                 fun p1  ->
                   match uu____54551 with
                   | (env1,acc) ->
                       let uu____54571 = translate_pat env1 p1  in
                       (match uu____54571 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54531 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____54598 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____54604 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____54618 =
            let uu____54620 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____54620
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____54618
          then
            let uu____54635 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____54635
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____54662) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____54680 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____54682 ->
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
          let uu____54706 =
            let uu____54713 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____54713)  in
          EApp uu____54706
