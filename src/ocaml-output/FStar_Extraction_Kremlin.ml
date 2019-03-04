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
    match projectee with | DGlobal _0 -> true | uu____46590 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____46702 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____46828 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____46936 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____47069 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____47187 -> false
  
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
    | uu____47329 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____47372 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____47383 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____47394 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____47405 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____47416 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____47427 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____47438 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____47449 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____47462 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____47484 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____47497 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____47521 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____47545 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____47567 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____47578 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____47589 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____47600 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____47611 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____47624 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____47655 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____47704 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____47738 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____47756 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____47800 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____47844 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____47888 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____47928 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____47958 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____47996 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____48038 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____48076 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____48118 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____48160 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____48220 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____48274 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____48310 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____48341 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____48352 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____48365 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____48387 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____48398 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____48410 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____48441 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____48501 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____48546 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____48584 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____48624 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____48659 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____48712 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____48751 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____48782 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____48827 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____48850 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____48874 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____48905 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____48916 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____48927 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____48938 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____48949 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____48960 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____48971 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____48982 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____48993 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____49004 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____49015 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____49026 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____49037 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____49048 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____49059 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____49070 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____49081 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____49092 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____49103 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____49114 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____49125 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____49136 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____49147 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____49158 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____49169 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____49180 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____49193 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____49216 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____49243 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____49286 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____49319 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____49365 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____49399 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____49410 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____49421 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____49432 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____49443 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____49454 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____49465 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____49476 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____49487 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____49498 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____49547 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____49567 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____49586 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____49606 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____49649 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____49660 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____49676 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____49709 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____49746 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____49810 -> false
  
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
  'Auu____49913 'Auu____49914 'Auu____49915 .
    ('Auu____49913 * 'Auu____49914 * 'Auu____49915) -> 'Auu____49913
  =
  fun uu____49926  ->
    match uu____49926 with | (x,uu____49934,uu____49935) -> x
  
let snd3 :
  'Auu____49945 'Auu____49946 'Auu____49947 .
    ('Auu____49945 * 'Auu____49946 * 'Auu____49947) -> 'Auu____49946
  =
  fun uu____49958  ->
    match uu____49958 with | (uu____49965,x,uu____49967) -> x
  
let thd3 :
  'Auu____49977 'Auu____49978 'Auu____49979 .
    ('Auu____49977 * 'Auu____49978 * 'Auu____49979) -> 'Auu____49979
  =
  fun uu____49990  ->
    match uu____49990 with | (uu____49997,uu____49998,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_50008  ->
    match uu___413_50008 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____50020 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_50030  ->
    match uu___414_50030 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____50039 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_50060  ->
    match uu___415_50060 with
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
    | uu____50105 -> FStar_Pervasives_Native.None
  
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
      let uu___575_50261 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_50261.names_t);
        module_name = (uu___575_50261.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_50275 = env  in
      {
        names = (uu___579_50275.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_50275.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____50290 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____50290 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_50314  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_50321 ->
          let uu____50323 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50323
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_50343  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_50352 ->
          let uu____50354 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____50354
  
let add_binders :
  'Auu____50365 . env -> (Prims.string * 'Auu____50365) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____50400  ->
             match uu____50400 with | (name,uu____50407) -> extend env1 name)
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
      | uu____50459 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____50678  ->
    match uu____50678 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____50727 = m  in
               match uu____50727 with
               | (path,uu____50742,uu____50743) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_50761  ->
                  match () with
                  | () ->
                      ((let uu____50765 =
                          let uu____50767 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____50767  in
                        if uu____50765
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____50773 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____50773))) ()
             with
             | e ->
                 ((let uu____50782 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____50782);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____50785  ->
    match uu____50785 with
    | (module_name,modul,uu____50800) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____50835 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_50849  ->
         match uu___416_50849 with
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
         | uu____50860 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____50864 =
      FStar_List.choose
        (fun uu___417_50871  ->
           match uu___417_50871 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____50878 -> FStar_Pervasives_Native.None) flags
       in
    match uu____50864 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____50891 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____50905 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____50907 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____50912) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____50939;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____50942;_} when
            FStar_Util.for_some
              (fun uu___418_50947  ->
                 match uu___418_50947 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____50950 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____50971 =
                let uu____50972 =
                  let uu____50993 = translate_cc meta  in
                  let uu____50996 = translate_flags meta  in
                  let uu____50999 = translate_type env t0  in
                  (uu____50993, uu____50996, name1, uu____50999)  in
                DExternal uu____50972  in
              FStar_Pervasives_Native.Some uu____50971
            else
              ((let uu____51015 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____51015);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51021;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____51024;
                FStar_Extraction_ML_Syntax.loc = uu____51025;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51027;_} ->
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
               let rec find_return_type eff i uu___419_51084 =
                 match uu___419_51084 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____51093,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____51113 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____51113 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____51139 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____51139
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____51157) ->
                           let uu____51158 = translate_flags meta  in
                           MustDisappear :: uu____51158
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____51161 = translate_flags meta  in
                           MustDisappear :: uu____51161
                       | uu____51164 -> translate_flags meta  in
                     try
                       (fun uu___780_51173  ->
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
                         ((let uu____51205 =
                             let uu____51211 =
                               let uu____51213 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____51213 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____51211)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____51205);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51239;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____51242;_} ->
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
                 (fun uu___807_51279  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____51303 =
                       let uu____51309 =
                         let uu____51311 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____51313 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____51311 uu____51313
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____51309)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____51303);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____51331;
            FStar_Extraction_ML_Syntax.mllb_def = uu____51332;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____51333;
            FStar_Extraction_ML_Syntax.print_typ = uu____51334;_} ->
            ((let uu____51341 =
                let uu____51347 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____51347)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____51341);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____51354 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____51354
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____51368 = ty  in
      match uu____51368 with
      | (uu____51371,uu____51372,uu____51373,uu____51374,flags,uu____51376)
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
                     (let uu____51450 =
                        let uu____51451 =
                          let uu____51471 = translate_flags flags1  in
                          let uu____51474 = translate_type env1 t  in
                          (name1, uu____51471, (FStar_List.length args),
                            uu____51474)
                           in
                        DTypeAlias uu____51451  in
                      FStar_Pervasives_Native.Some uu____51450)
             | (uu____51487,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____51532 =
                   let uu____51533 =
                     let uu____51565 = translate_flags flags1  in
                     let uu____51568 =
                       FStar_List.map
                         (fun uu____51600  ->
                            match uu____51600 with
                            | (f,t) ->
                                let uu____51620 =
                                  let uu____51626 = translate_type env1 t  in
                                  (uu____51626, false)  in
                                (f, uu____51620)) fields
                        in
                     (name1, uu____51565, (FStar_List.length args),
                       uu____51568)
                      in
                   DTypeFlat uu____51533  in
                 FStar_Pervasives_Native.Some uu____51532
             | (uu____51659,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____51709 =
                   let uu____51710 =
                     let uu____51749 =
                       FStar_List.map
                         (fun uu____51802  ->
                            match uu____51802 with
                            | (cons1,ts) ->
                                let uu____51850 =
                                  FStar_List.map
                                    (fun uu____51882  ->
                                       match uu____51882 with
                                       | (name2,t) ->
                                           let uu____51902 =
                                             let uu____51908 =
                                               translate_type env1 t  in
                                             (uu____51908, false)  in
                                           (name2, uu____51902)) ts
                                   in
                                (cons1, uu____51850)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____51749)
                      in
                   DTypeVariant uu____51710  in
                 FStar_Pervasives_Native.Some uu____51709
             | (uu____51961,name,_mangled_name,uu____51964,uu____51965,uu____51966)
                 ->
                 ((let uu____51982 =
                     let uu____51988 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____51988)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____51982);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____51996 = find_t env name  in TBound uu____51996
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____51999,t2) ->
          let uu____52001 =
            let uu____52006 = translate_type env t1  in
            let uu____52007 = translate_type env t2  in
            (uu____52006, uu____52007)  in
          TArrow uu____52001
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____52011 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52011 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____52018 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52018 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____52035 = FStar_Util.must (mk_width m)  in TInt uu____52035
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____52049 = FStar_Util.must (mk_width m)  in TInt uu____52049
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____52054 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52054 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____52058::arg::uu____52060::[],p) when
          (((let uu____52066 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52066 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____52071 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52071 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____52076 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52076 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____52081 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52081 = "FStar.HyperStack.ST.s_mref")
          -> let uu____52085 = translate_type env arg  in TBuf uu____52085
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____52087::[],p) when
          ((((((((((let uu____52093 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52093 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____52098 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52098 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____52103 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52103 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____52108 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52108 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____52113 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52113 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____52118 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52118 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____52123 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52123 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____52128 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52128 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____52133 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52133 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____52138 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52138 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____52143 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52143 = "FStar.HyperStack.ST.mmmref")
          -> let uu____52147 = translate_type env arg  in TBuf uu____52147
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____52149::uu____52150::[],p) when
          let uu____52154 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52154 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____52158 = translate_type env arg  in TBuf uu____52158
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____52165 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52165 = "FStar.Buffer.buffer") ||
                        (let uu____52170 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____52170 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____52175 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____52175 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____52180 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____52180 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____52185 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____52185 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____52190 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____52190 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____52195 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____52195 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____52200 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____52200 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____52205 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____52205 = "FStar.HyperStack.mmref"))
                ||
                (let uu____52210 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____52210 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____52215 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____52215 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____52220 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52220 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____52225 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52225 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____52230 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52230 = "FStar.HyperStack.ST.mmref")
          -> let uu____52234 = translate_type env arg  in TBuf uu____52234
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52235::arg::[],p) when
          (let uu____52242 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52242 = "FStar.HyperStack.s_ref") ||
            (let uu____52247 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52247 = "FStar.HyperStack.ST.s_ref")
          -> let uu____52251 = translate_type env arg  in TBuf uu____52251
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____52252::[],p) when
          let uu____52256 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52256 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____52308 = FStar_List.map (translate_type env) args  in
          TTuple uu____52308
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____52319 =
              let uu____52334 = FStar_List.map (translate_type env) args  in
              (lid, uu____52334)  in
            TApp uu____52319
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____52352 = FStar_List.map (translate_type env) ts  in
          TTuple uu____52352

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
    fun uu____52370  ->
      match uu____52370 with
      | (name,typ) ->
          let uu____52380 = translate_type env typ  in
          { name; typ = uu____52380; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____52387 = find env name  in EBound uu____52387
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____52401 =
            let uu____52406 = FStar_Util.must (mk_op op)  in
            let uu____52407 = FStar_Util.must (mk_width m)  in
            (uu____52406, uu____52407)  in
          EOp uu____52401
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____52417 =
            let uu____52422 = FStar_Util.must (mk_bool_op op)  in
            (uu____52422, Bool)  in
          EOp uu____52417
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
            let uu____52445 = translate_type env typ  in
            { name; typ = uu____52445; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____52472 =
            let uu____52483 = translate_expr env expr  in
            let uu____52484 = translate_branches env branches  in
            (uu____52483, uu____52484)  in
          EMatch uu____52472
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52498;
                  FStar_Extraction_ML_Syntax.loc = uu____52499;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____52501;
             FStar_Extraction_ML_Syntax.loc = uu____52502;_},arg::[])
          when
          let uu____52508 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52508 = "FStar.Dyn.undyn" ->
          let uu____52512 =
            let uu____52517 = translate_expr env arg  in
            let uu____52518 = translate_type env t  in
            (uu____52517, uu____52518)  in
          ECast uu____52512
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52520;
                  FStar_Extraction_ML_Syntax.loc = uu____52521;_},uu____52522);
             FStar_Extraction_ML_Syntax.mlty = uu____52523;
             FStar_Extraction_ML_Syntax.loc = uu____52524;_},uu____52525)
          when
          let uu____52534 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52534 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52539;
                  FStar_Extraction_ML_Syntax.loc = uu____52540;_},uu____52541);
             FStar_Extraction_ML_Syntax.mlty = uu____52542;
             FStar_Extraction_ML_Syntax.loc = uu____52543;_},arg::[])
          when
          ((let uu____52553 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52553 = "FStar.HyperStack.All.failwith") ||
             (let uu____52558 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52558 = "FStar.Error.unexpected"))
            ||
            (let uu____52563 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52563 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____52568;
               FStar_Extraction_ML_Syntax.loc = uu____52569;_} -> EAbortS msg
           | uu____52571 ->
               let print7 =
                 let uu____52573 =
                   let uu____52574 =
                     let uu____52575 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____52575
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____52574  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____52573
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
                  FStar_Extraction_ML_Syntax.mlty = uu____52582;
                  FStar_Extraction_ML_Syntax.loc = uu____52583;_},uu____52584);
             FStar_Extraction_ML_Syntax.mlty = uu____52585;
             FStar_Extraction_ML_Syntax.loc = uu____52586;_},e1::[])
          when
          (let uu____52596 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52596 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____52601 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52601 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52606;
                  FStar_Extraction_ML_Syntax.loc = uu____52607;_},uu____52608);
             FStar_Extraction_ML_Syntax.mlty = uu____52609;
             FStar_Extraction_ML_Syntax.loc = uu____52610;_},e1::e2::[])
          when
          (((let uu____52621 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52621 = "FStar.Buffer.index") ||
              (let uu____52626 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52626 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____52631 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52631 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____52636 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52636 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____52640 =
            let uu____52645 = translate_expr env e1  in
            let uu____52646 = translate_expr env e2  in
            (uu____52645, uu____52646)  in
          EBufRead uu____52640
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52648;
                  FStar_Extraction_ML_Syntax.loc = uu____52649;_},uu____52650);
             FStar_Extraction_ML_Syntax.mlty = uu____52651;
             FStar_Extraction_ML_Syntax.loc = uu____52652;_},e1::[])
          when
          let uu____52660 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52660 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____52664 =
            let uu____52669 = translate_expr env e1  in
            (uu____52669, (EConstant (UInt32, "0")))  in
          EBufRead uu____52664
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52673;
                  FStar_Extraction_ML_Syntax.loc = uu____52674;_},uu____52675);
             FStar_Extraction_ML_Syntax.mlty = uu____52676;
             FStar_Extraction_ML_Syntax.loc = uu____52677;_},e1::e2::[])
          when
          ((let uu____52688 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52688 = "FStar.Buffer.create") ||
             (let uu____52693 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52693 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____52698 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52698 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____52702 =
            let uu____52709 = translate_expr env e1  in
            let uu____52710 = translate_expr env e2  in
            (Stack, uu____52709, uu____52710)  in
          EBufCreate uu____52702
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52712;
                  FStar_Extraction_ML_Syntax.loc = uu____52713;_},uu____52714);
             FStar_Extraction_ML_Syntax.mlty = uu____52715;
             FStar_Extraction_ML_Syntax.loc = uu____52716;_},elen::[])
          when
          let uu____52724 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52724 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____52728 =
            let uu____52733 = translate_expr env elen  in
            (Stack, uu____52733)  in
          EBufCreateNoInit uu____52728
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
             FStar_Extraction_ML_Syntax.loc = uu____52739;_},init1::[])
          when
          let uu____52747 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52747 = "FStar.HyperStack.ST.salloc" ->
          let uu____52751 =
            let uu____52758 = translate_expr env init1  in
            (Stack, uu____52758, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52751
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52762;
                  FStar_Extraction_ML_Syntax.loc = uu____52763;_},uu____52764);
             FStar_Extraction_ML_Syntax.mlty = uu____52765;
             FStar_Extraction_ML_Syntax.loc = uu____52766;_},e2::[])
          when
          ((let uu____52776 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52776 = "FStar.Buffer.createL") ||
             (let uu____52781 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52781 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____52786 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52786 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____52790 =
            let uu____52797 =
              let uu____52800 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52800  in
            (Stack, uu____52797)  in
          EBufCreateL uu____52790
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52806;
                  FStar_Extraction_ML_Syntax.loc = uu____52807;_},uu____52808);
             FStar_Extraction_ML_Syntax.mlty = uu____52809;
             FStar_Extraction_ML_Syntax.loc = uu____52810;_},_erid::e2::[])
          when
          (let uu____52821 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____52821 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____52826 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52826 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____52830 =
            let uu____52837 =
              let uu____52840 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____52840  in
            (Eternal, uu____52837)  in
          EBufCreateL uu____52830
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52846;
                  FStar_Extraction_ML_Syntax.loc = uu____52847;_},uu____52848);
             FStar_Extraction_ML_Syntax.mlty = uu____52849;
             FStar_Extraction_ML_Syntax.loc = uu____52850;_},_rid::init1::[])
          when
          let uu____52859 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52859 = "FStar.HyperStack.ST.ralloc" ->
          let uu____52863 =
            let uu____52870 = translate_expr env init1  in
            (Eternal, uu____52870, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52863
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52874;
                  FStar_Extraction_ML_Syntax.loc = uu____52875;_},uu____52876);
             FStar_Extraction_ML_Syntax.mlty = uu____52877;
             FStar_Extraction_ML_Syntax.loc = uu____52878;_},_e0::e1::e2::[])
          when
          ((let uu____52890 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____52890 = "FStar.Buffer.rcreate") ||
             (let uu____52895 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52895 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____52900 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52900 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____52904 =
            let uu____52911 = translate_expr env e1  in
            let uu____52912 = translate_expr env e2  in
            (Eternal, uu____52911, uu____52912)  in
          EBufCreate uu____52904
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52914;
                  FStar_Extraction_ML_Syntax.loc = uu____52915;_},uu____52916);
             FStar_Extraction_ML_Syntax.mlty = uu____52917;
             FStar_Extraction_ML_Syntax.loc = uu____52918;_},_erid::elen::[])
          when
          let uu____52927 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52927 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____52931 =
            let uu____52936 = translate_expr env elen  in
            (Eternal, uu____52936)  in
          EBufCreateNoInit uu____52931
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52938;
                  FStar_Extraction_ML_Syntax.loc = uu____52939;_},uu____52940);
             FStar_Extraction_ML_Syntax.mlty = uu____52941;
             FStar_Extraction_ML_Syntax.loc = uu____52942;_},_rid::init1::[])
          when
          let uu____52951 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____52951 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____52955 =
            let uu____52962 = translate_expr env init1  in
            (ManuallyManaged, uu____52962, (EConstant (UInt32, "1")))  in
          EBufCreate uu____52955
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____52966;
                  FStar_Extraction_ML_Syntax.loc = uu____52967;_},uu____52968);
             FStar_Extraction_ML_Syntax.mlty = uu____52969;
             FStar_Extraction_ML_Syntax.loc = uu____52970;_},_e0::e1::e2::[])
          when
          (((let uu____52982 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52982 = "FStar.Buffer.rcreate_mm") ||
              (let uu____52987 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____52987 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____52992 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____52992 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____52997 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____52997 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____53001 =
            let uu____53008 = translate_expr env e1  in
            let uu____53009 = translate_expr env e2  in
            (ManuallyManaged, uu____53008, uu____53009)  in
          EBufCreate uu____53001
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53011;
                  FStar_Extraction_ML_Syntax.loc = uu____53012;_},uu____53013);
             FStar_Extraction_ML_Syntax.mlty = uu____53014;
             FStar_Extraction_ML_Syntax.loc = uu____53015;_},_erid::elen::[])
          when
          let uu____53024 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53024 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____53028 =
            let uu____53033 = translate_expr env elen  in
            (ManuallyManaged, uu____53033)  in
          EBufCreateNoInit uu____53028
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53035;
                  FStar_Extraction_ML_Syntax.loc = uu____53036;_},uu____53037);
             FStar_Extraction_ML_Syntax.mlty = uu____53038;
             FStar_Extraction_ML_Syntax.loc = uu____53039;_},e2::[])
          when
          let uu____53047 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53047 = "FStar.HyperStack.ST.rfree" ->
          let uu____53051 = translate_expr env e2  in EBufFree uu____53051
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53053;
                  FStar_Extraction_ML_Syntax.loc = uu____53054;_},uu____53055);
             FStar_Extraction_ML_Syntax.mlty = uu____53056;
             FStar_Extraction_ML_Syntax.loc = uu____53057;_},e2::[])
          when
          (let uu____53067 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____53067 = "FStar.Buffer.rfree") ||
            (let uu____53072 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53072 = "LowStar.Monotonic.Buffer.free")
          -> let uu____53076 = translate_expr env e2  in EBufFree uu____53076
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53078;
                  FStar_Extraction_ML_Syntax.loc = uu____53079;_},uu____53080);
             FStar_Extraction_ML_Syntax.mlty = uu____53081;
             FStar_Extraction_ML_Syntax.loc = uu____53082;_},e1::e2::_e3::[])
          when
          let uu____53092 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53092 = "FStar.Buffer.sub" ->
          let uu____53096 =
            let uu____53101 = translate_expr env e1  in
            let uu____53102 = translate_expr env e2  in
            (uu____53101, uu____53102)  in
          EBufSub uu____53096
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53104;
                  FStar_Extraction_ML_Syntax.loc = uu____53105;_},uu____53106);
             FStar_Extraction_ML_Syntax.mlty = uu____53107;
             FStar_Extraction_ML_Syntax.loc = uu____53108;_},e1::e2::_e3::[])
          when
          let uu____53118 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53118 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____53122 =
            let uu____53127 = translate_expr env e1  in
            let uu____53128 = translate_expr env e2  in
            (uu____53127, uu____53128)  in
          EBufSub uu____53122
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53130;
                  FStar_Extraction_ML_Syntax.loc = uu____53131;_},uu____53132);
             FStar_Extraction_ML_Syntax.mlty = uu____53133;
             FStar_Extraction_ML_Syntax.loc = uu____53134;_},e1::e2::[])
          when
          let uu____53143 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53143 = "FStar.Buffer.join" -> translate_expr env e1
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
          uu____53161 = "FStar.Buffer.offset" ->
          let uu____53165 =
            let uu____53170 = translate_expr env e1  in
            let uu____53171 = translate_expr env e2  in
            (uu____53170, uu____53171)  in
          EBufSub uu____53165
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53173;
                  FStar_Extraction_ML_Syntax.loc = uu____53174;_},uu____53175);
             FStar_Extraction_ML_Syntax.mlty = uu____53176;
             FStar_Extraction_ML_Syntax.loc = uu____53177;_},e1::e2::[])
          when
          let uu____53186 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53186 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____53190 =
            let uu____53195 = translate_expr env e1  in
            let uu____53196 = translate_expr env e2  in
            (uu____53195, uu____53196)  in
          EBufSub uu____53190
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53198;
                  FStar_Extraction_ML_Syntax.loc = uu____53199;_},uu____53200);
             FStar_Extraction_ML_Syntax.mlty = uu____53201;
             FStar_Extraction_ML_Syntax.loc = uu____53202;_},e1::e2::e3::[])
          when
          (((let uu____53214 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53214 = "FStar.Buffer.upd") ||
              (let uu____53219 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53219 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____53224 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53224 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____53229 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53229 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____53233 =
            let uu____53240 = translate_expr env e1  in
            let uu____53241 = translate_expr env e2  in
            let uu____53242 = translate_expr env e3  in
            (uu____53240, uu____53241, uu____53242)  in
          EBufWrite uu____53233
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53244;
                  FStar_Extraction_ML_Syntax.loc = uu____53245;_},uu____53246);
             FStar_Extraction_ML_Syntax.mlty = uu____53247;
             FStar_Extraction_ML_Syntax.loc = uu____53248;_},e1::e2::[])
          when
          let uu____53257 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53257 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____53261 =
            let uu____53268 = translate_expr env e1  in
            let uu____53269 = translate_expr env e2  in
            (uu____53268, (EConstant (UInt32, "0")), uu____53269)  in
          EBufWrite uu____53261
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53273;
             FStar_Extraction_ML_Syntax.loc = uu____53274;_},uu____53275::[])
          when
          let uu____53278 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53278 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53283;
             FStar_Extraction_ML_Syntax.loc = uu____53284;_},uu____53285::[])
          when
          let uu____53288 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53288 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53293;
                  FStar_Extraction_ML_Syntax.loc = uu____53294;_},uu____53295);
             FStar_Extraction_ML_Syntax.mlty = uu____53296;
             FStar_Extraction_ML_Syntax.loc = uu____53297;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____53311 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____53311 = "FStar.Buffer.blit") ||
             (let uu____53316 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53316 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____53321 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53321 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____53325 =
            let uu____53336 = translate_expr env e1  in
            let uu____53337 = translate_expr env e2  in
            let uu____53338 = translate_expr env e3  in
            let uu____53339 = translate_expr env e4  in
            let uu____53340 = translate_expr env e5  in
            (uu____53336, uu____53337, uu____53338, uu____53339, uu____53340)
             in
          EBufBlit uu____53325
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53342;
                  FStar_Extraction_ML_Syntax.loc = uu____53343;_},uu____53344);
             FStar_Extraction_ML_Syntax.mlty = uu____53345;
             FStar_Extraction_ML_Syntax.loc = uu____53346;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____53362 =
            let uu____53369 = translate_expr env e1  in
            let uu____53370 = translate_expr env e2  in
            let uu____53371 = translate_expr env e3  in
            (uu____53369, uu____53370, uu____53371)  in
          EBufFill uu____53362
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53373;
             FStar_Extraction_ML_Syntax.loc = uu____53374;_},uu____53375::[])
          when
          let uu____53378 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53378 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____53383;
                  FStar_Extraction_ML_Syntax.loc = uu____53384;_},uu____53385);
             FStar_Extraction_ML_Syntax.mlty = uu____53386;
             FStar_Extraction_ML_Syntax.loc = uu____53387;_},_ebuf::_eseq::[])
          when
          (((let uu____53398 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53398 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____53403 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____53403 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____53408 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____53408 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____53413 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____53413 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____53418;
             FStar_Extraction_ML_Syntax.loc = uu____53419;_},e1::[])
          when
          let uu____53423 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____53423 = "Obj.repr" ->
          let uu____53427 =
            let uu____53432 = translate_expr env e1  in (uu____53432, TAny)
             in
          ECast uu____53427
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53435;
             FStar_Extraction_ML_Syntax.loc = uu____53436;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____53452 = FStar_Util.must (mk_width m)  in
          let uu____53453 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____53452 uu____53453 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____53455;
             FStar_Extraction_ML_Syntax.loc = uu____53456;_},args)
          when is_bool_op op ->
          let uu____53470 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____53470 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53472;
             FStar_Extraction_ML_Syntax.loc = uu____53473;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53475;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53476;_}::[])
          when is_machine_int m ->
          let uu____53501 =
            let uu____53507 = FStar_Util.must (mk_width m)  in
            (uu____53507, c)  in
          EConstant uu____53501
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____53510;
             FStar_Extraction_ML_Syntax.loc = uu____53511;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53513;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53514;_}::[])
          when is_machine_int m ->
          let uu____53539 =
            let uu____53545 = FStar_Util.must (mk_width m)  in
            (uu____53545, c)  in
          EConstant uu____53539
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53547;
             FStar_Extraction_ML_Syntax.loc = uu____53548;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53550;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53551;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53564 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53566;
             FStar_Extraction_ML_Syntax.loc = uu____53567;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53569;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53570;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53587 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53589;
             FStar_Extraction_ML_Syntax.loc = uu____53590;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53592;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53593;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____53608 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____53610;
             FStar_Extraction_ML_Syntax.loc = uu____53611;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____53613;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____53614;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____53629 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____53632;
             FStar_Extraction_ML_Syntax.loc = uu____53633;_},arg::[])
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
            let uu____53661 =
              let uu____53666 = translate_expr env arg  in
              (uu____53666, (TInt UInt64))  in
            ECast uu____53661
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____53671 =
                 let uu____53676 = translate_expr env arg  in
                 (uu____53676, (TInt UInt32))  in
               ECast uu____53671)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____53681 =
                   let uu____53686 = translate_expr env arg  in
                   (uu____53686, (TInt UInt16))  in
                 ECast uu____53681)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____53691 =
                     let uu____53696 = translate_expr env arg  in
                     (uu____53696, (TInt UInt8))  in
                   ECast uu____53691)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____53701 =
                       let uu____53706 = translate_expr env arg  in
                       (uu____53706, (TInt Int64))  in
                     ECast uu____53701)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____53711 =
                         let uu____53716 = translate_expr env arg  in
                         (uu____53716, (TInt Int32))  in
                       ECast uu____53711)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____53721 =
                           let uu____53726 = translate_expr env arg  in
                           (uu____53726, (TInt Int16))  in
                         ECast uu____53721)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____53731 =
                             let uu____53736 = translate_expr env arg  in
                             (uu____53736, (TInt Int8))  in
                           ECast uu____53731)
                        else
                          (let uu____53739 =
                             let uu____53746 =
                               let uu____53749 = translate_expr env arg  in
                               [uu____53749]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____53746)
                              in
                           EApp uu____53739)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____53769 =
            let uu____53776 = translate_expr env head1  in
            let uu____53777 = FStar_List.map (translate_expr env) args  in
            (uu____53776, uu____53777)  in
          EApp uu____53769
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____53788 =
            let uu____53795 = translate_expr env head1  in
            let uu____53796 = FStar_List.map (translate_type env) ty_args  in
            (uu____53795, uu____53796)  in
          ETypApp uu____53788
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____53804 =
            let uu____53809 = translate_expr env e1  in
            let uu____53810 = translate_type env t_to  in
            (uu____53809, uu____53810)  in
          ECast uu____53804
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____53811,fields) ->
          let uu____53833 =
            let uu____53845 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53846 =
              FStar_List.map
                (fun uu____53868  ->
                   match uu____53868 with
                   | (field,expr) ->
                       let uu____53883 = translate_expr env expr  in
                       (field, uu____53883)) fields
               in
            (uu____53845, uu____53846)  in
          EFlat uu____53833
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____53894 =
            let uu____53902 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53903 = translate_expr env e1  in
            (uu____53902, uu____53903, (FStar_Pervasives_Native.snd path))
             in
          EField uu____53894
      | FStar_Extraction_ML_Syntax.MLE_Let uu____53909 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____53922) ->
          let uu____53927 =
            let uu____53929 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____53929
             in
          failwith uu____53927
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____53941 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____53941
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____53947 = FStar_List.map (translate_expr env) es  in
          ETuple uu____53947
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____53950,cons1),es) ->
          let uu____53965 =
            let uu____53975 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____53976 = FStar_List.map (translate_expr env) es  in
            (uu____53975, cons1, uu____53976)  in
          ECons uu____53965
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____54002 =
            let uu____54011 = translate_expr env1 body  in
            let uu____54012 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____54011, uu____54012)  in
          EFun uu____54002
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____54022 =
            let uu____54029 = translate_expr env e1  in
            let uu____54030 = translate_expr env e2  in
            let uu____54031 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____54029, uu____54030, uu____54031)  in
          EIfThenElse uu____54022
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____54033 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____54041 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____54057 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____54075 =
              let uu____54090 = FStar_List.map (translate_type env) ts  in
              (lid, uu____54090)  in
            TApp uu____54075
          else TQualified lid
      | uu____54105 -> failwith "invalid argument: assert_lid"

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
    fun uu____54132  ->
      match uu____54132 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____54159 = translate_pat env pat  in
            (match uu____54159 with
             | (env1,pat1) ->
                 let uu____54170 = translate_expr env1 expr  in
                 (pat1, uu____54170))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_54178  ->
    match uu___420_54178 with
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
          let uu____54245 =
            let uu____54246 =
              let uu____54252 = translate_width sw  in (uu____54252, s)  in
            PConstant uu____54246  in
          (env, uu____54245)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____54262,cons1),ps) ->
          let uu____54277 =
            FStar_List.fold_left
              (fun uu____54297  ->
                 fun p1  ->
                   match uu____54297 with
                   | (env1,acc) ->
                       let uu____54317 = translate_pat env1 p1  in
                       (match uu____54317 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54277 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____54347,ps) ->
          let uu____54369 =
            FStar_List.fold_left
              (fun uu____54406  ->
                 fun uu____54407  ->
                   match (uu____54406, uu____54407) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____54487 = translate_pat env1 p1  in
                       (match uu____54487 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____54369 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____54558 =
            FStar_List.fold_left
              (fun uu____54578  ->
                 fun p1  ->
                   match uu____54578 with
                   | (env1,acc) ->
                       let uu____54598 = translate_pat env1 p1  in
                       (match uu____54598 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____54558 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____54625 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____54631 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____54645 =
            let uu____54647 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____54647
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____54645
          then
            let uu____54662 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____54662
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____54689) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____54707 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____54709 ->
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
          let uu____54733 =
            let uu____54740 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____54740)  in
          EApp uu____54733
