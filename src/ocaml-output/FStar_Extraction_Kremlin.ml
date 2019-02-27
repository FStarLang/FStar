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
    match projectee with | DGlobal _0 -> true | uu____46515 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____46627 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____46753 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____46861 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____46994 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____47112 -> false
  
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
    | uu____47254 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____47297 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____47308 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____47319 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____47330 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____47341 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____47352 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____47363 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____47374 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____47387 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____47409 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____47422 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____47446 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____47470 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____47492 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____47503 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____47514 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____47525 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____47536 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____47549 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____47580 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____47629 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____47663 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____47681 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____47725 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____47769 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____47813 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____47853 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____47883 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____47921 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____47963 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____48001 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____48043 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____48085 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____48145 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____48199 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____48235 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____48266 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____48277 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____48290 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____48312 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____48323 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____48335 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____48366 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____48426 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____48471 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____48509 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____48549 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____48584 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____48637 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____48676 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____48707 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____48752 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____48775 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____48799 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____48830 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____48841 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____48852 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____48863 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____48874 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____48885 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____48896 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____48907 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____48918 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____48929 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____48940 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____48951 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____48962 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____48973 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____48984 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____48995 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____49006 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____49017 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____49028 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____49039 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____49050 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____49061 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____49072 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____49083 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____49094 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____49105 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____49118 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____49141 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____49168 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____49211 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____49244 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____49290 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____49324 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____49335 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____49346 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____49357 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____49368 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____49379 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____49390 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____49401 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____49412 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____49423 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____49472 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____49492 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____49511 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____49531 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____49574 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____49585 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____49601 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____49634 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____49671 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____49735 -> false
  
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
  'Auu____49838 'Auu____49839 'Auu____49840 .
    ('Auu____49838 * 'Auu____49839 * 'Auu____49840) -> 'Auu____49838
  =
  fun uu____49851  ->
    match uu____49851 with | (x,uu____49859,uu____49860) -> x
  
let snd3 :
  'Auu____49870 'Auu____49871 'Auu____49872 .
    ('Auu____49870 * 'Auu____49871 * 'Auu____49872) -> 'Auu____49871
  =
  fun uu____49883  ->
    match uu____49883 with | (uu____49890,x,uu____49892) -> x
  
let thd3 :
  'Auu____49902 'Auu____49903 'Auu____49904 .
    ('Auu____49902 * 'Auu____49903 * 'Auu____49904) -> 'Auu____49904
  =
  fun uu____49915  ->
    match uu____49915 with | (uu____49922,uu____49923,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_49933  ->
    match uu___413_49933 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____49945 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_49955  ->
    match uu___414_49955 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____49964 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_49985  ->
    match uu___415_49985 with
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
    | uu____50030 -> FStar_Pervasives_Native.None
  
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
      let uu___575_50186 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_50186.names_t);
        module_name = (uu___575_50186.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_50200 = env  in
      {
        names = (uu___579_50200.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_50200.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____50215 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____50215 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_50239  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_50246 ->
          let uu____50248 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50248
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_50268  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_50277 ->
          let uu____50279 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50279
  
let add_binders :
  'Auu____50290 . env -> (Prims.string * 'Auu____50290) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____50325  ->
             match uu____50325 with | (name,uu____50332) -> extend env1 name)
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
      | uu____50384 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____50603  ->
    match uu____50603 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____50652 = m  in
               match uu____50652 with
               | (path,uu____50667,uu____50668) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_50686  ->
                  match () with
                  | () ->
                      ((let uu____50690 =
                          let uu____50692 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____50692  in
                        if uu____50690
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____50698 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____50698))) ()
             with
             | e ->
                 ((let uu____50707 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____50707);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____50710  ->
    match uu____50710 with
    | (module_name,modul,uu____50725) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____50760 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_50774  ->
         match uu___416_50774 with
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
         | uu____50785 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____50789 =
      FStar_List.choose
        (fun uu___417_50796  ->
           match uu___417_50796 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____50803 -> FStar_Pervasives_Native.None) flags
       in
    match uu____50789 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____50816 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____50830 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____50832 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____50837) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50864;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____50867;_} when
            FStar_Util.for_some
              (fun uu___418_50872  ->
                 match uu___418_50872 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____50875 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____50896 =
                let uu____50897 =
                  let uu____50918 = translate_cc meta  in
                  let uu____50921 = translate_flags meta  in
                  let uu____50924 = translate_type env t0  in
                  (uu____50918, uu____50921, name1, uu____50924)  in
                DExternal uu____50897  in
              FStar_Pervasives_Native.Some uu____50896
            else
              ((let uu____50940 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____50940);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50946;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____50949;
                FStar_Extraction_ML_Syntax.loc = uu____50950;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____50952;_} ->
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
               let rec find_return_type eff i uu___419_51009 =
                 match uu___419_51009 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____51018,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____51038 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____51038 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____51064 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____51064
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____51082) ->
                           let uu____51083 = translate_flags meta  in
                           MustDisappear :: uu____51083
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____51086 = translate_flags meta  in
                           MustDisappear :: uu____51086
                       | uu____51089 -> translate_flags meta  in
                     try
                       (fun uu___780_51098  ->
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
                         ((let uu____51130 =
                             let uu____51136 =
                               let uu____51138 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____51138 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____51136)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____51130);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51164;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51167;_} ->
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
                 (fun uu___807_51204  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____51228 =
                       let uu____51234 =
                         let uu____51236 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____51238 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____51236 uu____51238
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____51234)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____51228);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51256;
            FStar_Extraction_ML_Syntax.mllb_def = uu____51257;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____51258;
            FStar_Extraction_ML_Syntax.print_typ = uu____51259;_} ->
            ((let uu____51266 =
                let uu____51272 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____51272)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____51266);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____51279 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____51279
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____51293 = ty  in
      match uu____51293 with
      | (uu____51296,uu____51297,uu____51298,uu____51299,flags,uu____51301)
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
                     (let uu____51375 =
                        let uu____51376 =
                          let uu____51396 = translate_flags flags1  in
                          let uu____51399 = translate_type env1 t  in
                          (name1, uu____51396, (FStar_List.length args),
                            uu____51399)
                           in
                        DTypeAlias uu____51376  in
                      FStar_Pervasives_Native.Some uu____51375)
             | (uu____51412,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____51457 =
                   let uu____51458 =
                     let uu____51490 = translate_flags flags1  in
                     let uu____51493 =
                       FStar_List.map
                         (fun uu____51525  ->
                            match uu____51525 with
                            | (f,t) ->
                                let uu____51545 =
                                  let uu____51551 = translate_type env1 t  in
                                  (uu____51551, false)  in
                                (f, uu____51545)) fields
                        in
                     (name1, uu____51490, (FStar_List.length args),
                       uu____51493)
                      in
                   DTypeFlat uu____51458  in
                 FStar_Pervasives_Native.Some uu____51457
             | (uu____51584,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____51634 =
                   let uu____51635 =
                     let uu____51674 =
                       FStar_List.map
                         (fun uu____51727  ->
                            match uu____51727 with
                            | (cons1,ts) ->
                                let uu____51775 =
                                  FStar_List.map
                                    (fun uu____51807  ->
                                       match uu____51807 with
                                       | (name2,t) ->
                                           let uu____51827 =
                                             let uu____51833 =
                                               translate_type env1 t  in
                                             (uu____51833, false)  in
                                           (name2, uu____51827)) ts
                                   in
                                (cons1, uu____51775)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____51674)
                      in
                   DTypeVariant uu____51635  in
                 FStar_Pervasives_Native.Some uu____51634
             | (uu____51886,name,_mangled_name,uu____51889,uu____51890,uu____51891)
                 ->
                 ((let uu____51907 =
                     let uu____51913 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____51913)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____51907);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____51921 = find_t env name  in TBound uu____51921
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____51924,t2) ->
          let uu____51926 =
            let uu____51931 = translate_type env t1  in
            let uu____51932 = translate_type env t2  in
            (uu____51931, uu____51932)  in
          TArrow uu____51926
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____51936 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____51936 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____51943 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____51943 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____51960 = FStar_Util.must (mk_width m)  in TInt uu____51960
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____51974 = FStar_Util.must (mk_width m)  in TInt uu____51974
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____51979 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____51979 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____51983::arg::uu____51985::[],p) when
          (((let uu____51991 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____51991 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____51996 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____51996 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____52001 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52001 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____52006 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52006 = "FStar.HyperStack.ST.s_mref")
          -> let uu____52010 = translate_type env arg  in TBuf uu____52010
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____52012::[],p) when
          ((((((((((let uu____52018 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52018 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____52023 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52023 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____52028 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52028 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____52033 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52033 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____52038 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52038 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____52043 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52043 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____52048 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52048 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____52053 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52053 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____52058 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52058 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____52063 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52063 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____52068 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52068 = "FStar.HyperStack.ST.mmmref")
          -> let uu____52072 = translate_type env arg  in TBuf uu____52072
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____52074::uu____52075::[],p) when
          let uu____52079 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52079 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____52083 = translate_type env arg  in TBuf uu____52083
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____52090 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52090 = "FStar.Buffer.buffer") ||
                        (let uu____52095 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____52095 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____52100 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____52100 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____52105 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52105 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____52110 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52110 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____52115 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52115 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____52120 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52120 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____52125 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52125 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____52130 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52130 = "FStar.HyperStack.mmref"))
                ||
                (let uu____52135 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52135 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____52140 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52140 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____52145 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52145 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____52150 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52150 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____52155 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52155 = "FStar.HyperStack.ST.mmref")
          -> let uu____52159 = translate_type env arg  in TBuf uu____52159
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52160::arg::[],p) when
          (let uu____52167 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52167 = "FStar.HyperStack.s_ref") ||
            (let uu____52172 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52172 = "FStar.HyperStack.ST.s_ref")
          -> let uu____52176 = translate_type env arg  in TBuf uu____52176
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52177::[],p) when
          let uu____52181 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52181 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____52233 = FStar_List.map (translate_type env) args  in
          TTuple uu____52233
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____52244 =
              let uu____52259 = FStar_List.map (translate_type env) args  in
              (lid, uu____52259)  in
            TApp uu____52244
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____52277 = FStar_List.map (translate_type env) ts  in
          TTuple uu____52277

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
    fun uu____52295  ->
      match uu____52295 with
      | (name,typ) ->
          let uu____52305 = translate_type env typ  in
          { name; typ = uu____52305; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____52312 = find env name  in EBound uu____52312
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____52326 =
            let uu____52331 = FStar_Util.must (mk_op op)  in
            let uu____52332 = FStar_Util.must (mk_width m)  in
            (uu____52331, uu____52332)  in
          EOp uu____52326
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____52342 =
            let uu____52347 = FStar_Util.must (mk_bool_op op)  in
            (uu____52347, Bool)  in
          EOp uu____52342
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
            let uu____52370 = translate_type env typ  in
            { name; typ = uu____52370; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____52397 =
            let uu____52408 = translate_expr env expr  in
            let uu____52409 = translate_branches env branches  in
            (uu____52408, uu____52409)  in
          EMatch uu____52397
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52423;
                  FStar_Extraction_ML_Syntax.loc = uu____52424;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____52426;
             FStar_Extraction_ML_Syntax.loc = uu____52427;_},arg::[])
          when
          let uu____52433 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52433 = "FStar.Dyn.undyn" ->
          let uu____52437 =
            let uu____52442 = translate_expr env arg  in
            let uu____52443 = translate_type env t  in
            (uu____52442, uu____52443)  in
          ECast uu____52437
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52445;
                  FStar_Extraction_ML_Syntax.loc = uu____52446;_},uu____52447);
             FStar_Extraction_ML_Syntax.mlty = uu____52448;
             FStar_Extraction_ML_Syntax.loc = uu____52449;_},uu____52450)
          when
          let uu____52459 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52459 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52464;
                  FStar_Extraction_ML_Syntax.loc = uu____52465;_},uu____52466);
             FStar_Extraction_ML_Syntax.mlty = uu____52467;
             FStar_Extraction_ML_Syntax.loc = uu____52468;_},arg::[])
          when
          ((let uu____52478 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52478 = "FStar.HyperStack.All.failwith") ||
             (let uu____52483 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52483 = "FStar.Error.unexpected"))
            ||
            (let uu____52488 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52488 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____52493;
               FStar_Extraction_ML_Syntax.loc = uu____52494;_} -> EAbortS msg
           | uu____52496 ->
               let print7 =
                 let uu____52498 =
                   let uu____52499 =
                     let uu____52500 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____52500
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____52499  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____52498
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
                  FStar_Extraction_ML_Syntax.mlty = uu____52507;
                  FStar_Extraction_ML_Syntax.loc = uu____52508;_},uu____52509);
             FStar_Extraction_ML_Syntax.mlty = uu____52510;
             FStar_Extraction_ML_Syntax.loc = uu____52511;_},e1::[])
          when
          (let uu____52521 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52521 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____52526 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52526 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52531;
                  FStar_Extraction_ML_Syntax.loc = uu____52532;_},uu____52533);
             FStar_Extraction_ML_Syntax.mlty = uu____52534;
             FStar_Extraction_ML_Syntax.loc = uu____52535;_},e1::e2::[])
          when
          (((let uu____52546 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52546 = "FStar.Buffer.index") ||
              (let uu____52551 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52551 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____52556 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52556 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____52561 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52561 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____52565 =
            let uu____52570 = translate_expr env e1  in
            let uu____52571 = translate_expr env e2  in
            (uu____52570, uu____52571)  in
          EBufRead uu____52565
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52573;
                  FStar_Extraction_ML_Syntax.loc = uu____52574;_},uu____52575);
             FStar_Extraction_ML_Syntax.mlty = uu____52576;
             FStar_Extraction_ML_Syntax.loc = uu____52577;_},e1::[])
          when
          let uu____52585 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52585 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____52589 =
            let uu____52594 = translate_expr env e1  in
            (uu____52594, (EConstant (UInt32, "0")))  in
          EBufRead uu____52589
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52598;
                  FStar_Extraction_ML_Syntax.loc = uu____52599;_},uu____52600);
             FStar_Extraction_ML_Syntax.mlty = uu____52601;
             FStar_Extraction_ML_Syntax.loc = uu____52602;_},e1::e2::[])
          when
          ((let uu____52613 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52613 = "FStar.Buffer.create") ||
             (let uu____52618 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52618 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____52623 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52623 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____52627 =
            let uu____52634 = translate_expr env e1  in
            let uu____52635 = translate_expr env e2  in
            (Stack, uu____52634, uu____52635)  in
          EBufCreate uu____52627
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52637;
                  FStar_Extraction_ML_Syntax.loc = uu____52638;_},uu____52639);
             FStar_Extraction_ML_Syntax.mlty = uu____52640;
             FStar_Extraction_ML_Syntax.loc = uu____52641;_},elen::[])
          when
          let uu____52649 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52649 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____52653 =
            let uu____52658 = translate_expr env elen  in
            (Stack, uu____52658)  in
          EBufCreateNoInit uu____52653
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52660;
                  FStar_Extraction_ML_Syntax.loc = uu____52661;_},uu____52662);
             FStar_Extraction_ML_Syntax.mlty = uu____52663;
             FStar_Extraction_ML_Syntax.loc = uu____52664;_},init1::[])
          when
          let uu____52672 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52672 = "FStar.HyperStack.ST.salloc" ->
          let uu____52676 =
            let uu____52683 = translate_expr env init1  in
            (Stack, uu____52683, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52676
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52687;
                  FStar_Extraction_ML_Syntax.loc = uu____52688;_},uu____52689);
             FStar_Extraction_ML_Syntax.mlty = uu____52690;
             FStar_Extraction_ML_Syntax.loc = uu____52691;_},e2::[])
          when
          ((let uu____52701 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52701 = "FStar.Buffer.createL") ||
             (let uu____52706 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52706 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____52711 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52711 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____52715 =
            let uu____52722 =
              let uu____52725 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52725  in
            (Stack, uu____52722)  in
          EBufCreateL uu____52715
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52731;
                  FStar_Extraction_ML_Syntax.loc = uu____52732;_},uu____52733);
             FStar_Extraction_ML_Syntax.mlty = uu____52734;
             FStar_Extraction_ML_Syntax.loc = uu____52735;_},_erid::e2::[])
          when
          (let uu____52746 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52746 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____52751 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52751 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____52755 =
            let uu____52762 =
              let uu____52765 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52765  in
            (Eternal, uu____52762)  in
          EBufCreateL uu____52755
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52771;
                  FStar_Extraction_ML_Syntax.loc = uu____52772;_},uu____52773);
             FStar_Extraction_ML_Syntax.mlty = uu____52774;
             FStar_Extraction_ML_Syntax.loc = uu____52775;_},_rid::init1::[])
          when
          let uu____52784 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52784 = "FStar.HyperStack.ST.ralloc" ->
          let uu____52788 =
            let uu____52795 = translate_expr env init1  in
            (Eternal, uu____52795, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52788
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52799;
                  FStar_Extraction_ML_Syntax.loc = uu____52800;_},uu____52801);
             FStar_Extraction_ML_Syntax.mlty = uu____52802;
             FStar_Extraction_ML_Syntax.loc = uu____52803;_},_e0::e1::e2::[])
          when
          ((let uu____52815 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52815 = "FStar.Buffer.rcreate") ||
             (let uu____52820 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52820 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____52825 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52825 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____52829 =
            let uu____52836 = translate_expr env e1  in
            let uu____52837 = translate_expr env e2  in
            (Eternal, uu____52836, uu____52837)  in
          EBufCreate uu____52829
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52839;
                  FStar_Extraction_ML_Syntax.loc = uu____52840;_},uu____52841);
             FStar_Extraction_ML_Syntax.mlty = uu____52842;
             FStar_Extraction_ML_Syntax.loc = uu____52843;_},_erid::elen::[])
          when
          let uu____52852 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52852 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____52856 =
            let uu____52861 = translate_expr env elen  in
            (Eternal, uu____52861)  in
          EBufCreateNoInit uu____52856
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52863;
                  FStar_Extraction_ML_Syntax.loc = uu____52864;_},uu____52865);
             FStar_Extraction_ML_Syntax.mlty = uu____52866;
             FStar_Extraction_ML_Syntax.loc = uu____52867;_},_rid::init1::[])
          when
          let uu____52876 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52876 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____52880 =
            let uu____52887 = translate_expr env init1  in
            (ManuallyManaged, uu____52887, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52880
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52891;
                  FStar_Extraction_ML_Syntax.loc = uu____52892;_},uu____52893);
             FStar_Extraction_ML_Syntax.mlty = uu____52894;
             FStar_Extraction_ML_Syntax.loc = uu____52895;_},_e0::e1::e2::[])
          when
          (((let uu____52907 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52907 = "FStar.Buffer.rcreate_mm") ||
              (let uu____52912 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52912 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____52917 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52917 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____52922 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52922 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____52926 =
            let uu____52933 = translate_expr env e1  in
            let uu____52934 = translate_expr env e2  in
            (ManuallyManaged, uu____52933, uu____52934)  in
          EBufCreate uu____52926
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52936;
                  FStar_Extraction_ML_Syntax.loc = uu____52937;_},uu____52938);
             FStar_Extraction_ML_Syntax.mlty = uu____52939;
             FStar_Extraction_ML_Syntax.loc = uu____52940;_},_erid::elen::[])
          when
          let uu____52949 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52949 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____52953 =
            let uu____52958 = translate_expr env elen  in
            (ManuallyManaged, uu____52958)  in
          EBufCreateNoInit uu____52953
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
             FStar_Extraction_ML_Syntax.loc = uu____52964;_},e2::[])
          when
          let uu____52972 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52972 = "FStar.HyperStack.ST.rfree" ->
          let uu____52976 = translate_expr env e2  in EBufFree uu____52976
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52978;
                  FStar_Extraction_ML_Syntax.loc = uu____52979;_},uu____52980);
             FStar_Extraction_ML_Syntax.mlty = uu____52981;
             FStar_Extraction_ML_Syntax.loc = uu____52982;_},e2::[])
          when
          (let uu____52992 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52992 = "FStar.Buffer.rfree") ||
            (let uu____52997 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52997 = "LowStar.Monotonic.Buffer.free")
          -> let uu____53001 = translate_expr env e2  in EBufFree uu____53001
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53003;
                  FStar_Extraction_ML_Syntax.loc = uu____53004;_},uu____53005);
             FStar_Extraction_ML_Syntax.mlty = uu____53006;
             FStar_Extraction_ML_Syntax.loc = uu____53007;_},e1::e2::_e3::[])
          when
          let uu____53017 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53017 = "FStar.Buffer.sub" ->
          let uu____53021 =
            let uu____53026 = translate_expr env e1  in
            let uu____53027 = translate_expr env e2  in
            (uu____53026, uu____53027)  in
          EBufSub uu____53021
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
             FStar_Extraction_ML_Syntax.loc = uu____53033;_},e1::e2::_e3::[])
          when
          let uu____53043 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53043 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____53047 =
            let uu____53052 = translate_expr env e1  in
            let uu____53053 = translate_expr env e2  in
            (uu____53052, uu____53053)  in
          EBufSub uu____53047
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53055;
                  FStar_Extraction_ML_Syntax.loc = uu____53056;_},uu____53057);
             FStar_Extraction_ML_Syntax.mlty = uu____53058;
             FStar_Extraction_ML_Syntax.loc = uu____53059;_},e1::e2::[])
          when
          let uu____53068 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53068 = "FStar.Buffer.join" -> translate_expr env e1
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
             FStar_Extraction_ML_Syntax.loc = uu____53077;_},e1::e2::[])
          when
          let uu____53086 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53086 = "FStar.Buffer.offset" ->
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
             FStar_Extraction_ML_Syntax.loc = uu____53102;_},e1::e2::[])
          when
          let uu____53111 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53111 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____53115 =
            let uu____53120 = translate_expr env e1  in
            let uu____53121 = translate_expr env e2  in
            (uu____53120, uu____53121)  in
          EBufSub uu____53115
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53123;
                  FStar_Extraction_ML_Syntax.loc = uu____53124;_},uu____53125);
             FStar_Extraction_ML_Syntax.mlty = uu____53126;
             FStar_Extraction_ML_Syntax.loc = uu____53127;_},e1::e2::e3::[])
          when
          (((let uu____53139 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53139 = "FStar.Buffer.upd") ||
              (let uu____53144 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53144 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____53149 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53149 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____53154 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53154 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____53158 =
            let uu____53165 = translate_expr env e1  in
            let uu____53166 = translate_expr env e2  in
            let uu____53167 = translate_expr env e3  in
            (uu____53165, uu____53166, uu____53167)  in
          EBufWrite uu____53158
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53169;
                  FStar_Extraction_ML_Syntax.loc = uu____53170;_},uu____53171);
             FStar_Extraction_ML_Syntax.mlty = uu____53172;
             FStar_Extraction_ML_Syntax.loc = uu____53173;_},e1::e2::[])
          when
          let uu____53182 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53182 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____53186 =
            let uu____53193 = translate_expr env e1  in
            let uu____53194 = translate_expr env e2  in
            (uu____53193, (EConstant (UInt32, "0")), uu____53194)  in
          EBufWrite uu____53186
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53198;
             FStar_Extraction_ML_Syntax.loc = uu____53199;_},uu____53200::[])
          when
          let uu____53203 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53203 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53208;
             FStar_Extraction_ML_Syntax.loc = uu____53209;_},uu____53210::[])
          when
          let uu____53213 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53213 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53218;
                  FStar_Extraction_ML_Syntax.loc = uu____53219;_},uu____53220);
             FStar_Extraction_ML_Syntax.mlty = uu____53221;
             FStar_Extraction_ML_Syntax.loc = uu____53222;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____53236 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____53236 = "FStar.Buffer.blit") ||
             (let uu____53241 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53241 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____53246 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53246 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____53250 =
            let uu____53261 = translate_expr env e1  in
            let uu____53262 = translate_expr env e2  in
            let uu____53263 = translate_expr env e3  in
            let uu____53264 = translate_expr env e4  in
            let uu____53265 = translate_expr env e5  in
            (uu____53261, uu____53262, uu____53263, uu____53264, uu____53265)
             in
          EBufBlit uu____53250
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53267;
                  FStar_Extraction_ML_Syntax.loc = uu____53268;_},uu____53269);
             FStar_Extraction_ML_Syntax.mlty = uu____53270;
             FStar_Extraction_ML_Syntax.loc = uu____53271;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____53287 =
            let uu____53294 = translate_expr env e1  in
            let uu____53295 = translate_expr env e2  in
            let uu____53296 = translate_expr env e3  in
            (uu____53294, uu____53295, uu____53296)  in
          EBufFill uu____53287
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53298;
             FStar_Extraction_ML_Syntax.loc = uu____53299;_},uu____53300::[])
          when
          let uu____53303 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53303 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53308;
                  FStar_Extraction_ML_Syntax.loc = uu____53309;_},uu____53310);
             FStar_Extraction_ML_Syntax.mlty = uu____53311;
             FStar_Extraction_ML_Syntax.loc = uu____53312;_},_ebuf::_eseq::[])
          when
          (((let uu____53323 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53323 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____53328 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53328 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____53333 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53333 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____53338 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53338 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53343;
             FStar_Extraction_ML_Syntax.loc = uu____53344;_},e1::[])
          when
          let uu____53348 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53348 = "Obj.repr" ->
          let uu____53352 =
            let uu____53357 = translate_expr env e1  in (uu____53357, TAny)
             in
          ECast uu____53352
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53360;
             FStar_Extraction_ML_Syntax.loc = uu____53361;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____53377 = FStar_Util.must (mk_width m)  in
          let uu____53378 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____53377 uu____53378 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53380;
             FStar_Extraction_ML_Syntax.loc = uu____53381;_},args)
          when is_bool_op op ->
          let uu____53395 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____53395 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53397;
             FStar_Extraction_ML_Syntax.loc = uu____53398;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53400;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53401;_}::[])
          when is_machine_int m ->
          let uu____53426 =
            let uu____53432 = FStar_Util.must (mk_width m)  in
            (uu____53432, c)  in
          EConstant uu____53426
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53435;
             FStar_Extraction_ML_Syntax.loc = uu____53436;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53438;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53439;_}::[])
          when is_machine_int m ->
          let uu____53464 =
            let uu____53470 = FStar_Util.must (mk_width m)  in
            (uu____53470, c)  in
          EConstant uu____53464
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53472;
             FStar_Extraction_ML_Syntax.loc = uu____53473;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53475;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53476;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53489 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53491;
             FStar_Extraction_ML_Syntax.loc = uu____53492;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53494;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53495;_}::[])
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
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53514;
             FStar_Extraction_ML_Syntax.loc = uu____53515;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53517;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53518;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53533 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____53536;
             FStar_Extraction_ML_Syntax.loc = uu____53537;_},arg::[])
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
            let uu____53565 =
              let uu____53570 = translate_expr env arg  in
              (uu____53570, (TInt UInt64))  in
            ECast uu____53565
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____53575 =
                 let uu____53580 = translate_expr env arg  in
                 (uu____53580, (TInt UInt32))  in
               ECast uu____53575)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____53585 =
                   let uu____53590 = translate_expr env arg  in
                   (uu____53590, (TInt UInt16))  in
                 ECast uu____53585)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____53595 =
                     let uu____53600 = translate_expr env arg  in
                     (uu____53600, (TInt UInt8))  in
                   ECast uu____53595)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____53605 =
                       let uu____53610 = translate_expr env arg  in
                       (uu____53610, (TInt Int64))  in
                     ECast uu____53605)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____53615 =
                         let uu____53620 = translate_expr env arg  in
                         (uu____53620, (TInt Int32))  in
                       ECast uu____53615)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____53625 =
                           let uu____53630 = translate_expr env arg  in
                           (uu____53630, (TInt Int16))  in
                         ECast uu____53625)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____53635 =
                             let uu____53640 = translate_expr env arg  in
                             (uu____53640, (TInt Int8))  in
                           ECast uu____53635)
                        else
                          (let uu____53643 =
                             let uu____53650 =
                               let uu____53653 = translate_expr env arg  in
                               [uu____53653]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____53650)
                              in
                           EApp uu____53643)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____53673 =
            let uu____53680 = translate_expr env head1  in
            let uu____53681 = FStar_List.map (translate_expr env) args  in
            (uu____53680, uu____53681)  in
          EApp uu____53673
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____53692 =
            let uu____53699 = translate_expr env head1  in
            let uu____53700 = FStar_List.map (translate_type env) ty_args  in
            (uu____53699, uu____53700)  in
          ETypApp uu____53692
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____53708 =
            let uu____53713 = translate_expr env e1  in
            let uu____53714 = translate_type env t_to  in
            (uu____53713, uu____53714)  in
          ECast uu____53708
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____53715,fields) ->
          let uu____53737 =
            let uu____53749 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53750 =
              FStar_List.map
                (fun uu____53772  ->
                   match uu____53772 with
                   | (field,expr) ->
                       let uu____53787 = translate_expr env expr  in
                       (field, uu____53787)) fields
               in
            (uu____53749, uu____53750)  in
          EFlat uu____53737
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____53798 =
            let uu____53806 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53807 = translate_expr env e1  in
            (uu____53806, uu____53807, (FStar_Pervasives_Native.snd path))
             in
          EField uu____53798
      | FStar_Extraction_ML_Syntax.MLE_Let uu____53813 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____53826) ->
          let uu____53831 =
            let uu____53833 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____53833
             in
          failwith uu____53831
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____53845 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____53845
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____53851 = FStar_List.map (translate_expr env) es  in
          ETuple uu____53851
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____53854,cons1),es) ->
          let uu____53869 =
            let uu____53879 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53880 = FStar_List.map (translate_expr env) es  in
            (uu____53879, cons1, uu____53880)  in
          ECons uu____53869
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____53906 =
            let uu____53915 = translate_expr env1 body  in
            let uu____53916 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____53915, uu____53916)  in
          EFun uu____53906
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____53926 =
            let uu____53933 = translate_expr env e1  in
            let uu____53934 = translate_expr env e2  in
            let uu____53935 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____53933, uu____53934, uu____53935)  in
          EIfThenElse uu____53926
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____53937 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____53945 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____53961 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____53979 =
              let uu____53994 = FStar_List.map (translate_type env) ts  in
              (lid, uu____53994)  in
            TApp uu____53979
          else TQualified lid
      | uu____54009 -> failwith "invalid argument: assert_lid"

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
    fun uu____54036  ->
      match uu____54036 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____54063 = translate_pat env pat  in
            (match uu____54063 with
             | (env1,pat1) ->
                 let uu____54074 = translate_expr env1 expr  in
                 (pat1, uu____54074))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_54082  ->
    match uu___420_54082 with
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
          let uu____54149 =
            let uu____54150 =
              let uu____54156 = translate_width sw  in (uu____54156, s)  in
            PConstant uu____54150  in
          (env, uu____54149)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____54166,cons1),ps) ->
          let uu____54181 =
            FStar_List.fold_left
              (fun uu____54201  ->
                 fun p1  ->
                   match uu____54201 with
                   | (env1,acc) ->
                       let uu____54221 = translate_pat env1 p1  in
                       (match uu____54221 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54181 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____54251,ps) ->
          let uu____54273 =
            FStar_List.fold_left
              (fun uu____54310  ->
                 fun uu____54311  ->
                   match (uu____54310, uu____54311) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____54391 = translate_pat env1 p1  in
                       (match uu____54391 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____54273 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____54462 =
            FStar_List.fold_left
              (fun uu____54482  ->
                 fun p1  ->
                   match uu____54482 with
                   | (env1,acc) ->
                       let uu____54502 = translate_pat env1 p1  in
                       (match uu____54502 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54462 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____54529 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____54535 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____54549 =
            let uu____54551 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____54551
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____54549
          then
            let uu____54566 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____54566
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____54593) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____54611 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____54613 ->
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
          let uu____54637 =
            let uu____54644 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____54644)  in
          EApp uu____54637
