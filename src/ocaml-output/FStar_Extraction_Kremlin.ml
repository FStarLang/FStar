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
    match projectee with | DGlobal _0 -> true | uu____46505 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____46617 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____46743 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____46851 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____46984 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____47102 -> false
  
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
    | uu____47244 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____47287 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____47298 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____47309 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____47320 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____47331 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____47342 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____47353 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____47364 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____47377 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____47399 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____47412 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____47436 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____47460 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____47482 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____47493 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____47504 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____47515 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____47528 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____47559 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____47608 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____47642 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____47660 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____47704 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____47748 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____47792 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____47832 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____47862 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____47900 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____47942 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____47980 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____48022 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____48064 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____48124 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____48178 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____48214 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____48245 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____48256 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____48269 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____48291 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____48302 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____48314 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____48345 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____48405 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____48450 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____48488 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____48528 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____48563 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____48616 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____48655 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____48686 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____48731 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____48754 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____48778 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____48809 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____48820 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____48831 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____48842 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____48853 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____48864 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____48875 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____48886 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____48897 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____48908 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____48919 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____48930 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____48941 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____48952 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____48963 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____48974 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____48985 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____48996 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____49007 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____49018 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____49029 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____49040 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____49051 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____49062 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____49073 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____49084 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____49097 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____49120 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____49147 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____49190 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____49223 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____49269 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____49303 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____49314 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____49325 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____49336 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____49347 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____49358 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____49369 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____49380 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____49391 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____49402 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____49451 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____49471 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____49490 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____49510 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____49553 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____49564 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____49580 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____49613 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____49650 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____49714 -> false
  
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
  'Auu____49817 'Auu____49818 'Auu____49819 .
    ('Auu____49817 * 'Auu____49818 * 'Auu____49819) -> 'Auu____49817
  =
  fun uu____49830  ->
    match uu____49830 with | (x,uu____49838,uu____49839) -> x
  
let snd3 :
  'Auu____49849 'Auu____49850 'Auu____49851 .
    ('Auu____49849 * 'Auu____49850 * 'Auu____49851) -> 'Auu____49850
  =
  fun uu____49862  ->
    match uu____49862 with | (uu____49869,x,uu____49871) -> x
  
let thd3 :
  'Auu____49881 'Auu____49882 'Auu____49883 .
    ('Auu____49881 * 'Auu____49882 * 'Auu____49883) -> 'Auu____49883
  =
  fun uu____49894  ->
    match uu____49894 with | (uu____49901,uu____49902,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_49912  ->
    match uu___413_49912 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____49924 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_49934  ->
    match uu___414_49934 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____49943 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_49964  ->
    match uu___415_49964 with
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
    | uu____50009 -> FStar_Pervasives_Native.None
  
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
      let uu___575_50165 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_50165.names_t);
        module_name = (uu___575_50165.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_50179 = env  in
      {
        names = (uu___579_50179.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_50179.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____50194 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____50194 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_50218  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_50225 ->
          let uu____50227 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50227
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_50247  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_50256 ->
          let uu____50258 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50258
  
let add_binders :
  'Auu____50269 . env -> (Prims.string * 'Auu____50269) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____50304  ->
             match uu____50304 with | (name,uu____50311) -> extend env1 name)
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
      | uu____50363 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____50582  ->
    match uu____50582 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____50631 = m  in
               match uu____50631 with
               | (path,uu____50646,uu____50647) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_50665  ->
                  match () with
                  | () ->
                      ((let uu____50669 =
                          let uu____50671 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____50671  in
                        if uu____50669
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____50677 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____50677))) ()
             with
             | e ->
                 ((let uu____50686 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____50686);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____50689  ->
    match uu____50689 with
    | (module_name,modul,uu____50704) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____50739 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_50753  ->
         match uu___416_50753 with
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
         | uu____50764 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____50768 =
      FStar_List.choose
        (fun uu___417_50775  ->
           match uu___417_50775 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____50782 -> FStar_Pervasives_Native.None) flags
       in
    match uu____50768 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____50795 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____50809 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____50811 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____50816) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50843;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____50846;_} when
            FStar_Util.for_some
              (fun uu___418_50851  ->
                 match uu___418_50851 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____50854 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____50875 =
                let uu____50876 =
                  let uu____50897 = translate_cc meta  in
                  let uu____50900 = translate_flags meta  in
                  let uu____50903 = translate_type env t0  in
                  (uu____50897, uu____50900, name1, uu____50903)  in
                DExternal uu____50876  in
              FStar_Pervasives_Native.Some uu____50875
            else
              ((let uu____50919 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____50919);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50925;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____50928;
                FStar_Extraction_ML_Syntax.loc = uu____50929;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____50931;_} ->
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
               let rec find_return_type eff i uu___419_50988 =
                 match uu___419_50988 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____50997,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____51017 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____51017 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____51043 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____51043
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____51061) ->
                           let uu____51062 = translate_flags meta  in
                           MustDisappear :: uu____51062
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____51065 = translate_flags meta  in
                           MustDisappear :: uu____51065
                       | uu____51068 -> translate_flags meta  in
                     try
                       (fun uu___779_51077  ->
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
                         ((let uu____51109 =
                             let uu____51115 =
                               let uu____51117 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____51117 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____51115)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____51109);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51143;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51146;_} ->
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
                 (fun uu___806_51183  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____51207 =
                       let uu____51213 =
                         let uu____51215 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____51217 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____51215 uu____51217
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____51213)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____51207);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51235;
            FStar_Extraction_ML_Syntax.mllb_def = uu____51236;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____51237;
            FStar_Extraction_ML_Syntax.print_typ = uu____51238;_} ->
            ((let uu____51245 =
                let uu____51251 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____51251)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____51245);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____51258 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____51258
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____51272 = ty  in
      match uu____51272 with
      | (uu____51275,uu____51276,uu____51277,uu____51278,flags,uu____51280)
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
                     (let uu____51354 =
                        let uu____51355 =
                          let uu____51375 = translate_flags flags1  in
                          let uu____51378 = translate_type env1 t  in
                          (name1, uu____51375, (FStar_List.length args),
                            uu____51378)
                           in
                        DTypeAlias uu____51355  in
                      FStar_Pervasives_Native.Some uu____51354)
             | (uu____51391,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____51436 =
                   let uu____51437 =
                     let uu____51469 = translate_flags flags1  in
                     let uu____51472 =
                       FStar_List.map
                         (fun uu____51504  ->
                            match uu____51504 with
                            | (f,t) ->
                                let uu____51524 =
                                  let uu____51530 = translate_type env1 t  in
                                  (uu____51530, false)  in
                                (f, uu____51524)) fields
                        in
                     (name1, uu____51469, (FStar_List.length args),
                       uu____51472)
                      in
                   DTypeFlat uu____51437  in
                 FStar_Pervasives_Native.Some uu____51436
             | (uu____51563,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____51613 =
                   let uu____51614 =
                     let uu____51653 =
                       FStar_List.map
                         (fun uu____51706  ->
                            match uu____51706 with
                            | (cons1,ts) ->
                                let uu____51754 =
                                  FStar_List.map
                                    (fun uu____51786  ->
                                       match uu____51786 with
                                       | (name2,t) ->
                                           let uu____51806 =
                                             let uu____51812 =
                                               translate_type env1 t  in
                                             (uu____51812, false)  in
                                           (name2, uu____51806)) ts
                                   in
                                (cons1, uu____51754)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____51653)
                      in
                   DTypeVariant uu____51614  in
                 FStar_Pervasives_Native.Some uu____51613
             | (uu____51865,name,_mangled_name,uu____51868,uu____51869,uu____51870)
                 ->
                 ((let uu____51886 =
                     let uu____51892 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____51892)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____51886);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____51900 = find_t env name  in TBound uu____51900
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____51903,t2) ->
          let uu____51905 =
            let uu____51910 = translate_type env t1  in
            let uu____51911 = translate_type env t2  in
            (uu____51910, uu____51911)  in
          TArrow uu____51905
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____51915 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____51915 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____51922 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____51922 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____51939 = FStar_Util.must (mk_width m)  in TInt uu____51939
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____51953 = FStar_Util.must (mk_width m)  in TInt uu____51953
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____51958 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____51958 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____51962::arg::uu____51964::[],p) when
          (((let uu____51970 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____51970 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____51975 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____51975 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____51980 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____51980 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____51985 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____51985 = "FStar.HyperStack.ST.s_mref")
          -> let uu____51989 = translate_type env arg  in TBuf uu____51989
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____51991::[],p) when
          ((((((((((let uu____51997 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____51997 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____52002 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52002 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____52007 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52007 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____52012 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52012 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____52017 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52017 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____52022 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52022 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____52027 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52027 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____52032 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52032 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____52037 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52037 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____52042 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52042 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____52047 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52047 = "FStar.HyperStack.ST.mmmref")
          -> let uu____52051 = translate_type env arg  in TBuf uu____52051
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____52053::uu____52054::[],p) when
          let uu____52058 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52058 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____52062 = translate_type env arg  in TBuf uu____52062
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____52069 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52069 = "FStar.Buffer.buffer") ||
                        (let uu____52074 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____52074 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____52079 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____52079 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____52084 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52084 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____52089 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52089 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____52094 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52094 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____52099 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52099 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____52104 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52104 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____52109 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52109 = "FStar.HyperStack.mmref"))
                ||
                (let uu____52114 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52114 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____52119 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52119 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____52124 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52124 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____52129 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52129 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____52134 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52134 = "FStar.HyperStack.ST.mmref")
          -> let uu____52138 = translate_type env arg  in TBuf uu____52138
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52139::arg::[],p) when
          (let uu____52146 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52146 = "FStar.HyperStack.s_ref") ||
            (let uu____52151 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52151 = "FStar.HyperStack.ST.s_ref")
          -> let uu____52155 = translate_type env arg  in TBuf uu____52155
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52156::[],p) when
          let uu____52160 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52160 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____52212 = FStar_List.map (translate_type env) args  in
          TTuple uu____52212
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____52223 =
              let uu____52238 = FStar_List.map (translate_type env) args  in
              (lid, uu____52238)  in
            TApp uu____52223
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____52256 = FStar_List.map (translate_type env) ts  in
          TTuple uu____52256

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
    fun uu____52274  ->
      match uu____52274 with
      | (name,typ) ->
          let uu____52284 = translate_type env typ  in
          { name; typ = uu____52284; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____52291 = find env name  in EBound uu____52291
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____52305 =
            let uu____52310 = FStar_Util.must (mk_op op)  in
            let uu____52311 = FStar_Util.must (mk_width m)  in
            (uu____52310, uu____52311)  in
          EOp uu____52305
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____52321 =
            let uu____52326 = FStar_Util.must (mk_bool_op op)  in
            (uu____52326, Bool)  in
          EOp uu____52321
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
            let uu____52349 = translate_type env typ  in
            { name; typ = uu____52349; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____52376 =
            let uu____52387 = translate_expr env expr  in
            let uu____52388 = translate_branches env branches  in
            (uu____52387, uu____52388)  in
          EMatch uu____52376
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52402;
                  FStar_Extraction_ML_Syntax.loc = uu____52403;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____52405;
             FStar_Extraction_ML_Syntax.loc = uu____52406;_},arg::[])
          when
          let uu____52412 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52412 = "FStar.Dyn.undyn" ->
          let uu____52416 =
            let uu____52421 = translate_expr env arg  in
            let uu____52422 = translate_type env t  in
            (uu____52421, uu____52422)  in
          ECast uu____52416
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52424;
                  FStar_Extraction_ML_Syntax.loc = uu____52425;_},uu____52426);
             FStar_Extraction_ML_Syntax.mlty = uu____52427;
             FStar_Extraction_ML_Syntax.loc = uu____52428;_},uu____52429)
          when
          let uu____52438 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52438 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52443;
                  FStar_Extraction_ML_Syntax.loc = uu____52444;_},uu____52445);
             FStar_Extraction_ML_Syntax.mlty = uu____52446;
             FStar_Extraction_ML_Syntax.loc = uu____52447;_},arg::[])
          when
          ((let uu____52457 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52457 = "FStar.HyperStack.All.failwith") ||
             (let uu____52462 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52462 = "FStar.Error.unexpected"))
            ||
            (let uu____52467 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52467 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____52472;
               FStar_Extraction_ML_Syntax.loc = uu____52473;_} -> EAbortS msg
           | uu____52475 ->
               let print7 =
                 let uu____52477 =
                   let uu____52478 =
                     let uu____52479 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____52479
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____52478  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____52477
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
                  FStar_Extraction_ML_Syntax.mlty = uu____52486;
                  FStar_Extraction_ML_Syntax.loc = uu____52487;_},uu____52488);
             FStar_Extraction_ML_Syntax.mlty = uu____52489;
             FStar_Extraction_ML_Syntax.loc = uu____52490;_},e1::[])
          when
          (let uu____52500 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52500 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____52505 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52505 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52510;
                  FStar_Extraction_ML_Syntax.loc = uu____52511;_},uu____52512);
             FStar_Extraction_ML_Syntax.mlty = uu____52513;
             FStar_Extraction_ML_Syntax.loc = uu____52514;_},e1::e2::[])
          when
          (((let uu____52525 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52525 = "FStar.Buffer.index") ||
              (let uu____52530 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52530 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____52535 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52535 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____52540 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52540 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____52544 =
            let uu____52549 = translate_expr env e1  in
            let uu____52550 = translate_expr env e2  in
            (uu____52549, uu____52550)  in
          EBufRead uu____52544
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52552;
                  FStar_Extraction_ML_Syntax.loc = uu____52553;_},uu____52554);
             FStar_Extraction_ML_Syntax.mlty = uu____52555;
             FStar_Extraction_ML_Syntax.loc = uu____52556;_},e1::[])
          when
          let uu____52564 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52564 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____52568 =
            let uu____52573 = translate_expr env e1  in
            (uu____52573, (EConstant (UInt32, "0")))  in
          EBufRead uu____52568
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
             FStar_Extraction_ML_Syntax.loc = uu____52581;_},e1::e2::[])
          when
          ((let uu____52592 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52592 = "FStar.Buffer.create") ||
             (let uu____52597 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52597 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____52602 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52602 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____52606 =
            let uu____52613 = translate_expr env e1  in
            let uu____52614 = translate_expr env e2  in
            (Stack, uu____52613, uu____52614)  in
          EBufCreate uu____52606
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52616;
                  FStar_Extraction_ML_Syntax.loc = uu____52617;_},uu____52618);
             FStar_Extraction_ML_Syntax.mlty = uu____52619;
             FStar_Extraction_ML_Syntax.loc = uu____52620;_},elen::[])
          when
          let uu____52628 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52628 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____52632 =
            let uu____52637 = translate_expr env elen  in
            (Stack, uu____52637)  in
          EBufCreateNoInit uu____52632
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52639;
                  FStar_Extraction_ML_Syntax.loc = uu____52640;_},uu____52641);
             FStar_Extraction_ML_Syntax.mlty = uu____52642;
             FStar_Extraction_ML_Syntax.loc = uu____52643;_},init1::[])
          when
          let uu____52651 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52651 = "FStar.HyperStack.ST.salloc" ->
          let uu____52655 =
            let uu____52662 = translate_expr env init1  in
            (Stack, uu____52662, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52655
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52666;
                  FStar_Extraction_ML_Syntax.loc = uu____52667;_},uu____52668);
             FStar_Extraction_ML_Syntax.mlty = uu____52669;
             FStar_Extraction_ML_Syntax.loc = uu____52670;_},e2::[])
          when
          ((let uu____52680 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52680 = "FStar.Buffer.createL") ||
             (let uu____52685 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52685 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____52690 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52690 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____52694 =
            let uu____52701 =
              let uu____52704 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52704  in
            (Stack, uu____52701)  in
          EBufCreateL uu____52694
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52710;
                  FStar_Extraction_ML_Syntax.loc = uu____52711;_},uu____52712);
             FStar_Extraction_ML_Syntax.mlty = uu____52713;
             FStar_Extraction_ML_Syntax.loc = uu____52714;_},_erid::e2::[])
          when
          (let uu____52725 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52725 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____52730 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52730 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____52734 =
            let uu____52741 =
              let uu____52744 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52744  in
            (Eternal, uu____52741)  in
          EBufCreateL uu____52734
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52750;
                  FStar_Extraction_ML_Syntax.loc = uu____52751;_},uu____52752);
             FStar_Extraction_ML_Syntax.mlty = uu____52753;
             FStar_Extraction_ML_Syntax.loc = uu____52754;_},_rid::init1::[])
          when
          let uu____52763 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52763 = "FStar.HyperStack.ST.ralloc" ->
          let uu____52767 =
            let uu____52774 = translate_expr env init1  in
            (Eternal, uu____52774, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52767
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52778;
                  FStar_Extraction_ML_Syntax.loc = uu____52779;_},uu____52780);
             FStar_Extraction_ML_Syntax.mlty = uu____52781;
             FStar_Extraction_ML_Syntax.loc = uu____52782;_},_e0::e1::e2::[])
          when
          ((let uu____52794 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52794 = "FStar.Buffer.rcreate") ||
             (let uu____52799 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52799 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____52804 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52804 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____52808 =
            let uu____52815 = translate_expr env e1  in
            let uu____52816 = translate_expr env e2  in
            (Eternal, uu____52815, uu____52816)  in
          EBufCreate uu____52808
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52818;
                  FStar_Extraction_ML_Syntax.loc = uu____52819;_},uu____52820);
             FStar_Extraction_ML_Syntax.mlty = uu____52821;
             FStar_Extraction_ML_Syntax.loc = uu____52822;_},_erid::elen::[])
          when
          let uu____52831 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52831 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____52835 =
            let uu____52840 = translate_expr env elen  in
            (Eternal, uu____52840)  in
          EBufCreateNoInit uu____52835
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52842;
                  FStar_Extraction_ML_Syntax.loc = uu____52843;_},uu____52844);
             FStar_Extraction_ML_Syntax.mlty = uu____52845;
             FStar_Extraction_ML_Syntax.loc = uu____52846;_},_rid::init1::[])
          when
          let uu____52855 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52855 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____52859 =
            let uu____52866 = translate_expr env init1  in
            (ManuallyManaged, uu____52866, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52859
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52870;
                  FStar_Extraction_ML_Syntax.loc = uu____52871;_},uu____52872);
             FStar_Extraction_ML_Syntax.mlty = uu____52873;
             FStar_Extraction_ML_Syntax.loc = uu____52874;_},_e0::e1::e2::[])
          when
          (((let uu____52886 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52886 = "FStar.Buffer.rcreate_mm") ||
              (let uu____52891 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52891 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____52896 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52896 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____52901 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52901 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____52905 =
            let uu____52912 = translate_expr env e1  in
            let uu____52913 = translate_expr env e2  in
            (ManuallyManaged, uu____52912, uu____52913)  in
          EBufCreate uu____52905
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52915;
                  FStar_Extraction_ML_Syntax.loc = uu____52916;_},uu____52917);
             FStar_Extraction_ML_Syntax.mlty = uu____52918;
             FStar_Extraction_ML_Syntax.loc = uu____52919;_},_erid::elen::[])
          when
          let uu____52928 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52928 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____52932 =
            let uu____52937 = translate_expr env elen  in
            (ManuallyManaged, uu____52937)  in
          EBufCreateNoInit uu____52932
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
             FStar_Extraction_ML_Syntax.loc = uu____52943;_},e2::[])
          when
          let uu____52951 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52951 = "FStar.HyperStack.ST.rfree" ->
          let uu____52955 = translate_expr env e2  in EBufFree uu____52955
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52957;
                  FStar_Extraction_ML_Syntax.loc = uu____52958;_},uu____52959);
             FStar_Extraction_ML_Syntax.mlty = uu____52960;
             FStar_Extraction_ML_Syntax.loc = uu____52961;_},e2::[])
          when
          (let uu____52971 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52971 = "FStar.Buffer.rfree") ||
            (let uu____52976 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52976 = "LowStar.Monotonic.Buffer.free")
          -> let uu____52980 = translate_expr env e2  in EBufFree uu____52980
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52982;
                  FStar_Extraction_ML_Syntax.loc = uu____52983;_},uu____52984);
             FStar_Extraction_ML_Syntax.mlty = uu____52985;
             FStar_Extraction_ML_Syntax.loc = uu____52986;_},e1::e2::_e3::[])
          when
          let uu____52996 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52996 = "FStar.Buffer.sub" ->
          let uu____53000 =
            let uu____53005 = translate_expr env e1  in
            let uu____53006 = translate_expr env e2  in
            (uu____53005, uu____53006)  in
          EBufSub uu____53000
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
             FStar_Extraction_ML_Syntax.loc = uu____53012;_},e1::e2::_e3::[])
          when
          let uu____53022 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53022 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____53026 =
            let uu____53031 = translate_expr env e1  in
            let uu____53032 = translate_expr env e2  in
            (uu____53031, uu____53032)  in
          EBufSub uu____53026
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53034;
                  FStar_Extraction_ML_Syntax.loc = uu____53035;_},uu____53036);
             FStar_Extraction_ML_Syntax.mlty = uu____53037;
             FStar_Extraction_ML_Syntax.loc = uu____53038;_},e1::e2::[])
          when
          let uu____53047 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53047 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53052;
                  FStar_Extraction_ML_Syntax.loc = uu____53053;_},uu____53054);
             FStar_Extraction_ML_Syntax.mlty = uu____53055;
             FStar_Extraction_ML_Syntax.loc = uu____53056;_},e1::e2::[])
          when
          let uu____53065 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53065 = "FStar.Buffer.offset" ->
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
             FStar_Extraction_ML_Syntax.loc = uu____53081;_},e1::e2::[])
          when
          let uu____53090 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53090 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____53094 =
            let uu____53099 = translate_expr env e1  in
            let uu____53100 = translate_expr env e2  in
            (uu____53099, uu____53100)  in
          EBufSub uu____53094
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53102;
                  FStar_Extraction_ML_Syntax.loc = uu____53103;_},uu____53104);
             FStar_Extraction_ML_Syntax.mlty = uu____53105;
             FStar_Extraction_ML_Syntax.loc = uu____53106;_},e1::e2::e3::[])
          when
          (((let uu____53118 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53118 = "FStar.Buffer.upd") ||
              (let uu____53123 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53123 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____53128 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53128 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____53133 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53133 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____53137 =
            let uu____53144 = translate_expr env e1  in
            let uu____53145 = translate_expr env e2  in
            let uu____53146 = translate_expr env e3  in
            (uu____53144, uu____53145, uu____53146)  in
          EBufWrite uu____53137
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53148;
                  FStar_Extraction_ML_Syntax.loc = uu____53149;_},uu____53150);
             FStar_Extraction_ML_Syntax.mlty = uu____53151;
             FStar_Extraction_ML_Syntax.loc = uu____53152;_},e1::e2::[])
          when
          let uu____53161 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53161 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____53165 =
            let uu____53172 = translate_expr env e1  in
            let uu____53173 = translate_expr env e2  in
            (uu____53172, (EConstant (UInt32, "0")), uu____53173)  in
          EBufWrite uu____53165
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53177;
             FStar_Extraction_ML_Syntax.loc = uu____53178;_},uu____53179::[])
          when
          let uu____53182 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53182 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53187;
             FStar_Extraction_ML_Syntax.loc = uu____53188;_},uu____53189::[])
          when
          let uu____53192 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53192 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53197;
                  FStar_Extraction_ML_Syntax.loc = uu____53198;_},uu____53199);
             FStar_Extraction_ML_Syntax.mlty = uu____53200;
             FStar_Extraction_ML_Syntax.loc = uu____53201;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____53215 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____53215 = "FStar.Buffer.blit") ||
             (let uu____53220 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53220 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____53225 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53225 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____53229 =
            let uu____53240 = translate_expr env e1  in
            let uu____53241 = translate_expr env e2  in
            let uu____53242 = translate_expr env e3  in
            let uu____53243 = translate_expr env e4  in
            let uu____53244 = translate_expr env e5  in
            (uu____53240, uu____53241, uu____53242, uu____53243, uu____53244)
             in
          EBufBlit uu____53229
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53246;
                  FStar_Extraction_ML_Syntax.loc = uu____53247;_},uu____53248);
             FStar_Extraction_ML_Syntax.mlty = uu____53249;
             FStar_Extraction_ML_Syntax.loc = uu____53250;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____53266 =
            let uu____53273 = translate_expr env e1  in
            let uu____53274 = translate_expr env e2  in
            let uu____53275 = translate_expr env e3  in
            (uu____53273, uu____53274, uu____53275)  in
          EBufFill uu____53266
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53277;
             FStar_Extraction_ML_Syntax.loc = uu____53278;_},uu____53279::[])
          when
          let uu____53282 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53282 = "FStar.HyperStack.ST.get" -> EUnit
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
             FStar_Extraction_ML_Syntax.loc = uu____53291;_},_ebuf::_eseq::[])
          when
          (((let uu____53302 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53302 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____53307 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53307 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____53312 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53312 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____53317 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53317 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53322;
             FStar_Extraction_ML_Syntax.loc = uu____53323;_},e1::[])
          when
          let uu____53327 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53327 = "Obj.repr" ->
          let uu____53331 =
            let uu____53336 = translate_expr env e1  in (uu____53336, TAny)
             in
          ECast uu____53331
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53339;
             FStar_Extraction_ML_Syntax.loc = uu____53340;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____53356 = FStar_Util.must (mk_width m)  in
          let uu____53357 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____53356 uu____53357 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53359;
             FStar_Extraction_ML_Syntax.loc = uu____53360;_},args)
          when is_bool_op op ->
          let uu____53374 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____53374 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53376;
             FStar_Extraction_ML_Syntax.loc = uu____53377;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53379;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53380;_}::[])
          when is_machine_int m ->
          let uu____53405 =
            let uu____53411 = FStar_Util.must (mk_width m)  in
            (uu____53411, c)  in
          EConstant uu____53405
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53414;
             FStar_Extraction_ML_Syntax.loc = uu____53415;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53417;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53418;_}::[])
          when is_machine_int m ->
          let uu____53443 =
            let uu____53449 = FStar_Util.must (mk_width m)  in
            (uu____53449, c)  in
          EConstant uu____53443
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53451;
             FStar_Extraction_ML_Syntax.loc = uu____53452;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53454;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53455;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53468 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53470;
             FStar_Extraction_ML_Syntax.loc = uu____53471;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53473;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53474;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53491 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53493;
             FStar_Extraction_ML_Syntax.loc = uu____53494;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53496;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53497;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53512 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____53515;
             FStar_Extraction_ML_Syntax.loc = uu____53516;_},arg::[])
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
            let uu____53544 =
              let uu____53549 = translate_expr env arg  in
              (uu____53549, (TInt UInt64))  in
            ECast uu____53544
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____53554 =
                 let uu____53559 = translate_expr env arg  in
                 (uu____53559, (TInt UInt32))  in
               ECast uu____53554)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____53564 =
                   let uu____53569 = translate_expr env arg  in
                   (uu____53569, (TInt UInt16))  in
                 ECast uu____53564)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____53574 =
                     let uu____53579 = translate_expr env arg  in
                     (uu____53579, (TInt UInt8))  in
                   ECast uu____53574)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____53584 =
                       let uu____53589 = translate_expr env arg  in
                       (uu____53589, (TInt Int64))  in
                     ECast uu____53584)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____53594 =
                         let uu____53599 = translate_expr env arg  in
                         (uu____53599, (TInt Int32))  in
                       ECast uu____53594)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____53604 =
                           let uu____53609 = translate_expr env arg  in
                           (uu____53609, (TInt Int16))  in
                         ECast uu____53604)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____53614 =
                             let uu____53619 = translate_expr env arg  in
                             (uu____53619, (TInt Int8))  in
                           ECast uu____53614)
                        else
                          (let uu____53622 =
                             let uu____53629 =
                               let uu____53632 = translate_expr env arg  in
                               [uu____53632]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____53629)
                              in
                           EApp uu____53622)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____53652 =
            let uu____53659 = translate_expr env head1  in
            let uu____53660 = FStar_List.map (translate_expr env) args  in
            (uu____53659, uu____53660)  in
          EApp uu____53652
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____53671 =
            let uu____53678 = translate_expr env head1  in
            let uu____53679 = FStar_List.map (translate_type env) ty_args  in
            (uu____53678, uu____53679)  in
          ETypApp uu____53671
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____53687 =
            let uu____53692 = translate_expr env e1  in
            let uu____53693 = translate_type env t_to  in
            (uu____53692, uu____53693)  in
          ECast uu____53687
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____53694,fields) ->
          let uu____53716 =
            let uu____53728 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53729 =
              FStar_List.map
                (fun uu____53751  ->
                   match uu____53751 with
                   | (field,expr) ->
                       let uu____53766 = translate_expr env expr  in
                       (field, uu____53766)) fields
               in
            (uu____53728, uu____53729)  in
          EFlat uu____53716
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____53777 =
            let uu____53785 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53786 = translate_expr env e1  in
            (uu____53785, uu____53786, (FStar_Pervasives_Native.snd path))
             in
          EField uu____53777
      | FStar_Extraction_ML_Syntax.MLE_Let uu____53792 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____53805) ->
          let uu____53810 =
            let uu____53812 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____53812
             in
          failwith uu____53810
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____53824 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____53824
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____53830 = FStar_List.map (translate_expr env) es  in
          ETuple uu____53830
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____53833,cons1),es) ->
          let uu____53848 =
            let uu____53858 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53859 = FStar_List.map (translate_expr env) es  in
            (uu____53858, cons1, uu____53859)  in
          ECons uu____53848
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____53885 =
            let uu____53894 = translate_expr env1 body  in
            let uu____53895 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____53894, uu____53895)  in
          EFun uu____53885
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____53905 =
            let uu____53912 = translate_expr env e1  in
            let uu____53913 = translate_expr env e2  in
            let uu____53914 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____53912, uu____53913, uu____53914)  in
          EIfThenElse uu____53905
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____53916 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____53924 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____53940 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____53958 =
              let uu____53973 = FStar_List.map (translate_type env) ts  in
              (lid, uu____53973)  in
            TApp uu____53958
          else TQualified lid
      | uu____53988 -> failwith "invalid argument: assert_lid"

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
    fun uu____54015  ->
      match uu____54015 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____54042 = translate_pat env pat  in
            (match uu____54042 with
             | (env1,pat1) ->
                 let uu____54053 = translate_expr env1 expr  in
                 (pat1, uu____54053))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_54061  ->
    match uu___420_54061 with
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
          let uu____54128 =
            let uu____54129 =
              let uu____54135 = translate_width sw  in (uu____54135, s)  in
            PConstant uu____54129  in
          (env, uu____54128)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____54145,cons1),ps) ->
          let uu____54160 =
            FStar_List.fold_left
              (fun uu____54180  ->
                 fun p1  ->
                   match uu____54180 with
                   | (env1,acc) ->
                       let uu____54200 = translate_pat env1 p1  in
                       (match uu____54200 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54160 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____54230,ps) ->
          let uu____54252 =
            FStar_List.fold_left
              (fun uu____54289  ->
                 fun uu____54290  ->
                   match (uu____54289, uu____54290) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____54370 = translate_pat env1 p1  in
                       (match uu____54370 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____54252 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____54441 =
            FStar_List.fold_left
              (fun uu____54461  ->
                 fun p1  ->
                   match uu____54461 with
                   | (env1,acc) ->
                       let uu____54481 = translate_pat env1 p1  in
                       (match uu____54481 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54441 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____54508 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____54514 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____54528 =
            let uu____54530 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____54530
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____54528
          then
            let uu____54545 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____54545
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____54572) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____54590 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____54592 ->
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
          let uu____54616 =
            let uu____54623 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____54623)  in
          EApp uu____54616
