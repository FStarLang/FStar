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
    match projectee with | DGlobal _0 -> true | uu____42074 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____42185 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____42310 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____42417 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____42549 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____42666 -> false
  
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
    | uu____42807 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____42849 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____42860 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____42871 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____42882 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____42893 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____42904 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____42915 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____42926 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____42939 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____42960 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____42973 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____42996 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____43019 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____43040 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____43051 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____43062 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____43073 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____43084 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____43097 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____43127 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____43175 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____43208 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____43226 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____43269 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____43312 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____43355 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____43394 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____43423 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____43460 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____43501 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____43538 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____43579 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____43620 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____43679 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____43732 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____43767 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____43797 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____43808 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____43821 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____43842 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____43853 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____43865 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____43895 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____43954 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____43998 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____44035 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____44074 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____44108 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____44160 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____44198 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____44228 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____44272 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____44294 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____44317 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____44347 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____44358 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____44369 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____44380 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____44391 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____44402 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____44413 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____44424 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____44435 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____44446 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____44457 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____44468 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____44479 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____44490 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____44501 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____44512 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____44523 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____44534 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____44545 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____44556 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____44567 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____44578 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____44589 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____44600 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____44611 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____44622 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____44635 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____44657 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____44683 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____44725 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____44757 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____44802 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____44835 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____44846 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____44857 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____44868 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____44879 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____44890 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____44901 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____44912 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____44923 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____44934 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____44983 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____45002 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____45020 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____45040 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____45082 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____45093 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____45109 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____45141 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____45177 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____45240 -> false
  
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
  'Auu____45341 'Auu____45342 'Auu____45343 .
    ('Auu____45341 * 'Auu____45342 * 'Auu____45343) -> 'Auu____45341
  =
  fun uu____45354  ->
    match uu____45354 with | (x,uu____45362,uu____45363) -> x
  
let snd3 :
  'Auu____45373 'Auu____45374 'Auu____45375 .
    ('Auu____45373 * 'Auu____45374 * 'Auu____45375) -> 'Auu____45374
  =
  fun uu____45386  ->
    match uu____45386 with | (uu____45393,x,uu____45395) -> x
  
let thd3 :
  'Auu____45405 'Auu____45406 'Auu____45407 .
    ('Auu____45405 * 'Auu____45406 * 'Auu____45407) -> 'Auu____45407
  =
  fun uu____45418  ->
    match uu____45418 with | (uu____45425,uu____45426,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_45436  ->
    match uu___413_45436 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____45448 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_45458  ->
    match uu___414_45458 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____45467 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_45488  ->
    match uu___415_45488 with
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
    | uu____45533 -> FStar_Pervasives_Native.None
  
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
      let uu___575_45689 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_45689.names_t);
        module_name = (uu___575_45689.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_45703 = env  in
      {
        names = (uu___579_45703.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_45703.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____45718 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____45718 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_45742  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_45749 ->
          let uu____45751 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____45751
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_45771  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_45780 ->
          let uu____45782 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____45782
  
let add_binders :
  'Auu____45793 . env -> (Prims.string * 'Auu____45793) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____45828  ->
             match uu____45828 with | (name,uu____45835) -> extend env1 name)
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
      | uu____45887 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____46106  ->
    match uu____46106 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____46155 = m  in
               match uu____46155 with
               | (path,uu____46170,uu____46171) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_46189  ->
                  match () with
                  | () ->
                      ((let uu____46193 =
                          let uu____46195 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____46195  in
                        if uu____46193
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____46201 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____46201))) ()
             with
             | e ->
                 ((let uu____46210 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____46210);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____46213  ->
    match uu____46213 with
    | (module_name,modul,uu____46228) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____46263 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_46277  ->
         match uu___416_46277 with
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
         | uu____46288 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____46292 =
      FStar_List.choose
        (fun uu___417_46299  ->
           match uu___417_46299 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____46306 -> FStar_Pervasives_Native.None) flags
       in
    match uu____46292 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____46319 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____46333 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____46335 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____46340) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____46367;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____46370;_} when
            FStar_Util.for_some
              (fun uu___418_46375  ->
                 match uu___418_46375 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____46378 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____46399 =
                let uu____46400 =
                  let uu____46421 = translate_cc meta  in
                  let uu____46424 = translate_flags meta  in
                  let uu____46427 = translate_type env t0  in
                  (uu____46421, uu____46424, name1, uu____46427)  in
                DExternal uu____46400  in
              FStar_Pervasives_Native.Some uu____46399
            else
              ((let uu____46443 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____46443);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____46449;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____46452;
                FStar_Extraction_ML_Syntax.loc = uu____46453;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____46455;_} ->
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
               let rec find_return_type eff i uu___419_46512 =
                 match uu___419_46512 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____46521,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____46541 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____46541 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____46567 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____46567
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____46585) ->
                           let uu____46586 = translate_flags meta  in
                           MustDisappear :: uu____46586
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____46589 = translate_flags meta  in
                           MustDisappear :: uu____46589
                       | uu____46592 -> translate_flags meta  in
                     try
                       (fun uu___780_46601  ->
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
                         ((let uu____46633 =
                             let uu____46639 =
                               let uu____46641 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____46641 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____46639)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____46633);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____46667;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____46670;_} ->
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
                 (fun uu___807_46707  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____46731 =
                       let uu____46737 =
                         let uu____46739 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____46741 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____46739 uu____46741
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____46737)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____46731);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____46759;
            FStar_Extraction_ML_Syntax.mllb_def = uu____46760;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____46761;
            FStar_Extraction_ML_Syntax.print_typ = uu____46762;_} ->
            ((let uu____46769 =
                let uu____46775 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____46775)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____46769);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____46782 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____46782
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____46796 = ty  in
      match uu____46796 with
      | (uu____46799,uu____46800,uu____46801,uu____46802,flags,uu____46804)
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
                     (let uu____46878 =
                        let uu____46879 =
                          let uu____46899 = translate_flags flags1  in
                          let uu____46902 = translate_type env1 t  in
                          (name1, uu____46899, (FStar_List.length args),
                            uu____46902)
                           in
                        DTypeAlias uu____46879  in
                      FStar_Pervasives_Native.Some uu____46878)
             | (uu____46915,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____46960 =
                   let uu____46961 =
                     let uu____46993 = translate_flags flags1  in
                     let uu____46996 =
                       FStar_List.map
                         (fun uu____47028  ->
                            match uu____47028 with
                            | (f,t) ->
                                let uu____47048 =
                                  let uu____47054 = translate_type env1 t  in
                                  (uu____47054, false)  in
                                (f, uu____47048)) fields
                        in
                     (name1, uu____46993, (FStar_List.length args),
                       uu____46996)
                      in
                   DTypeFlat uu____46961  in
                 FStar_Pervasives_Native.Some uu____46960
             | (uu____47087,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____47137 =
                   let uu____47138 =
                     let uu____47177 =
                       FStar_List.map
                         (fun uu____47230  ->
                            match uu____47230 with
                            | (cons1,ts) ->
                                let uu____47278 =
                                  FStar_List.map
                                    (fun uu____47310  ->
                                       match uu____47310 with
                                       | (name2,t) ->
                                           let uu____47330 =
                                             let uu____47336 =
                                               translate_type env1 t  in
                                             (uu____47336, false)  in
                                           (name2, uu____47330)) ts
                                   in
                                (cons1, uu____47278)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____47177)
                      in
                   DTypeVariant uu____47138  in
                 FStar_Pervasives_Native.Some uu____47137
             | (uu____47389,name,_mangled_name,uu____47392,uu____47393,uu____47394)
                 ->
                 ((let uu____47410 =
                     let uu____47416 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____47416)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____47410);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____47424 = find_t env name  in TBound uu____47424
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____47427,t2) ->
          let uu____47429 =
            let uu____47434 = translate_type env t1  in
            let uu____47435 = translate_type env t2  in
            (uu____47434, uu____47435)  in
          TArrow uu____47429
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____47439 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47439 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____47446 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47446 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____47463 = FStar_Util.must (mk_width m)  in TInt uu____47463
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____47477 = FStar_Util.must (mk_width m)  in TInt uu____47477
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____47482 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47482 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____47486::arg::uu____47488::[],p) when
          (((let uu____47494 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47494 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____47499 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____47499 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____47504 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____47504 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____47509 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47509 = "FStar.HyperStack.ST.s_mref")
          -> let uu____47513 = translate_type env arg  in TBuf uu____47513
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____47515::[],p) when
          ((((((((((let uu____47521 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____47521 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____47526 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____47526 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____47531 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____47531 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____47536 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____47536 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____47541 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____47541 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____47546 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____47546 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____47551 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____47551 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____47556 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____47556 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____47561 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____47561 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____47566 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____47566 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____47571 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47571 = "FStar.HyperStack.ST.mmmref")
          -> let uu____47575 = translate_type env arg  in TBuf uu____47575
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____47577::uu____47578::[],p) when
          let uu____47582 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47582 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____47586 = translate_type env arg  in TBuf uu____47586
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____47593 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____47593 = "FStar.Buffer.buffer") ||
                        (let uu____47598 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____47598 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____47603 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____47603 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____47608 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____47608 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____47613 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____47613 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____47618 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____47618 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____47623 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____47623 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____47628 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____47628 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____47633 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____47633 = "FStar.HyperStack.mmref"))
                ||
                (let uu____47638 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____47638 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____47643 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____47643 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____47648 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____47648 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____47653 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____47653 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____47658 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47658 = "FStar.HyperStack.ST.mmref")
          -> let uu____47662 = translate_type env arg  in TBuf uu____47662
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____47663::arg::[],p) when
          (let uu____47670 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____47670 = "FStar.HyperStack.s_ref") ||
            (let uu____47675 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47675 = "FStar.HyperStack.ST.s_ref")
          -> let uu____47679 = translate_type env arg  in TBuf uu____47679
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____47680::[],p) when
          let uu____47684 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47684 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____47736 = FStar_List.map (translate_type env) args  in
          TTuple uu____47736
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____47747 =
              let uu____47762 = FStar_List.map (translate_type env) args  in
              (lid, uu____47762)  in
            TApp uu____47747
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____47780 = FStar_List.map (translate_type env) ts  in
          TTuple uu____47780

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
    fun uu____47798  ->
      match uu____47798 with
      | (name,typ) ->
          let uu____47808 = translate_type env typ  in
          { name; typ = uu____47808; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____47815 = find env name  in EBound uu____47815
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____47829 =
            let uu____47834 = FStar_Util.must (mk_op op)  in
            let uu____47835 = FStar_Util.must (mk_width m)  in
            (uu____47834, uu____47835)  in
          EOp uu____47829
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____47845 =
            let uu____47850 = FStar_Util.must (mk_bool_op op)  in
            (uu____47850, Bool)  in
          EOp uu____47845
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
            let uu____47873 = translate_type env typ  in
            { name; typ = uu____47873; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____47900 =
            let uu____47911 = translate_expr env expr  in
            let uu____47912 = translate_branches env branches  in
            (uu____47911, uu____47912)  in
          EMatch uu____47900
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____47926;
                  FStar_Extraction_ML_Syntax.loc = uu____47927;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____47929;
             FStar_Extraction_ML_Syntax.loc = uu____47930;_},arg::[])
          when
          let uu____47936 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47936 = "FStar.Dyn.undyn" ->
          let uu____47940 =
            let uu____47945 = translate_expr env arg  in
            let uu____47946 = translate_type env t  in
            (uu____47945, uu____47946)  in
          ECast uu____47940
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____47948;
                  FStar_Extraction_ML_Syntax.loc = uu____47949;_},uu____47950);
             FStar_Extraction_ML_Syntax.mlty = uu____47951;
             FStar_Extraction_ML_Syntax.loc = uu____47952;_},uu____47953)
          when
          let uu____47962 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47962 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____47967;
                  FStar_Extraction_ML_Syntax.loc = uu____47968;_},uu____47969);
             FStar_Extraction_ML_Syntax.mlty = uu____47970;
             FStar_Extraction_ML_Syntax.loc = uu____47971;_},arg::[])
          when
          ((let uu____47981 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____47981 = "FStar.HyperStack.All.failwith") ||
             (let uu____47986 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____47986 = "FStar.Error.unexpected"))
            ||
            (let uu____47991 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47991 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____47996;
               FStar_Extraction_ML_Syntax.loc = uu____47997;_} -> EAbortS msg
           | uu____47999 ->
               let print7 =
                 let uu____48001 =
                   let uu____48002 =
                     let uu____48003 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____48003
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____48002  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____48001
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
                  FStar_Extraction_ML_Syntax.mlty = uu____48010;
                  FStar_Extraction_ML_Syntax.loc = uu____48011;_},uu____48012);
             FStar_Extraction_ML_Syntax.mlty = uu____48013;
             FStar_Extraction_ML_Syntax.loc = uu____48014;_},e1::[])
          when
          (let uu____48024 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48024 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____48029 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48029 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48034;
                  FStar_Extraction_ML_Syntax.loc = uu____48035;_},uu____48036);
             FStar_Extraction_ML_Syntax.mlty = uu____48037;
             FStar_Extraction_ML_Syntax.loc = uu____48038;_},e1::e2::[])
          when
          (((let uu____48049 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48049 = "FStar.Buffer.index") ||
              (let uu____48054 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48054 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____48059 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48059 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____48064 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48064 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____48068 =
            let uu____48073 = translate_expr env e1  in
            let uu____48074 = translate_expr env e2  in
            (uu____48073, uu____48074)  in
          EBufRead uu____48068
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48076;
                  FStar_Extraction_ML_Syntax.loc = uu____48077;_},uu____48078);
             FStar_Extraction_ML_Syntax.mlty = uu____48079;
             FStar_Extraction_ML_Syntax.loc = uu____48080;_},e1::[])
          when
          let uu____48088 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48088 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____48092 =
            let uu____48097 = translate_expr env e1  in
            (uu____48097, (EConstant (UInt32, "0")))  in
          EBufRead uu____48092
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48101;
                  FStar_Extraction_ML_Syntax.loc = uu____48102;_},uu____48103);
             FStar_Extraction_ML_Syntax.mlty = uu____48104;
             FStar_Extraction_ML_Syntax.loc = uu____48105;_},e1::e2::[])
          when
          ((let uu____48116 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48116 = "FStar.Buffer.create") ||
             (let uu____48121 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48121 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____48126 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48126 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____48130 =
            let uu____48137 = translate_expr env e1  in
            let uu____48138 = translate_expr env e2  in
            (Stack, uu____48137, uu____48138)  in
          EBufCreate uu____48130
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48140;
                  FStar_Extraction_ML_Syntax.loc = uu____48141;_},uu____48142);
             FStar_Extraction_ML_Syntax.mlty = uu____48143;
             FStar_Extraction_ML_Syntax.loc = uu____48144;_},elen::[])
          when
          let uu____48152 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48152 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____48156 =
            let uu____48161 = translate_expr env elen  in
            (Stack, uu____48161)  in
          EBufCreateNoInit uu____48156
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48163;
                  FStar_Extraction_ML_Syntax.loc = uu____48164;_},uu____48165);
             FStar_Extraction_ML_Syntax.mlty = uu____48166;
             FStar_Extraction_ML_Syntax.loc = uu____48167;_},init1::[])
          when
          let uu____48175 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48175 = "FStar.HyperStack.ST.salloc" ->
          let uu____48179 =
            let uu____48186 = translate_expr env init1  in
            (Stack, uu____48186, (EConstant (UInt32, "1")))  in
          EBufCreate uu____48179
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48190;
                  FStar_Extraction_ML_Syntax.loc = uu____48191;_},uu____48192);
             FStar_Extraction_ML_Syntax.mlty = uu____48193;
             FStar_Extraction_ML_Syntax.loc = uu____48194;_},e2::[])
          when
          ((let uu____48204 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48204 = "FStar.Buffer.createL") ||
             (let uu____48209 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48209 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____48214 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48214 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____48218 =
            let uu____48225 =
              let uu____48228 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____48228  in
            (Stack, uu____48225)  in
          EBufCreateL uu____48218
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48234;
                  FStar_Extraction_ML_Syntax.loc = uu____48235;_},uu____48236);
             FStar_Extraction_ML_Syntax.mlty = uu____48237;
             FStar_Extraction_ML_Syntax.loc = uu____48238;_},_erid::e2::[])
          when
          (let uu____48249 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48249 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____48254 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48254 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____48258 =
            let uu____48265 =
              let uu____48268 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____48268  in
            (Eternal, uu____48265)  in
          EBufCreateL uu____48258
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48274;
                  FStar_Extraction_ML_Syntax.loc = uu____48275;_},uu____48276);
             FStar_Extraction_ML_Syntax.mlty = uu____48277;
             FStar_Extraction_ML_Syntax.loc = uu____48278;_},_rid::init1::[])
          when
          let uu____48287 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48287 = "FStar.HyperStack.ST.ralloc" ->
          let uu____48291 =
            let uu____48298 = translate_expr env init1  in
            (Eternal, uu____48298, (EConstant (UInt32, "1")))  in
          EBufCreate uu____48291
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48302;
                  FStar_Extraction_ML_Syntax.loc = uu____48303;_},uu____48304);
             FStar_Extraction_ML_Syntax.mlty = uu____48305;
             FStar_Extraction_ML_Syntax.loc = uu____48306;_},_e0::e1::e2::[])
          when
          ((let uu____48318 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48318 = "FStar.Buffer.rcreate") ||
             (let uu____48323 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48323 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____48328 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48328 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____48332 =
            let uu____48339 = translate_expr env e1  in
            let uu____48340 = translate_expr env e2  in
            (Eternal, uu____48339, uu____48340)  in
          EBufCreate uu____48332
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48342;
                  FStar_Extraction_ML_Syntax.loc = uu____48343;_},uu____48344);
             FStar_Extraction_ML_Syntax.mlty = uu____48345;
             FStar_Extraction_ML_Syntax.loc = uu____48346;_},_erid::elen::[])
          when
          let uu____48355 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48355 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____48359 =
            let uu____48364 = translate_expr env elen  in
            (Eternal, uu____48364)  in
          EBufCreateNoInit uu____48359
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48366;
                  FStar_Extraction_ML_Syntax.loc = uu____48367;_},uu____48368);
             FStar_Extraction_ML_Syntax.mlty = uu____48369;
             FStar_Extraction_ML_Syntax.loc = uu____48370;_},_rid::init1::[])
          when
          let uu____48379 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48379 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____48383 =
            let uu____48390 = translate_expr env init1  in
            (ManuallyManaged, uu____48390, (EConstant (UInt32, "1")))  in
          EBufCreate uu____48383
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48394;
                  FStar_Extraction_ML_Syntax.loc = uu____48395;_},uu____48396);
             FStar_Extraction_ML_Syntax.mlty = uu____48397;
             FStar_Extraction_ML_Syntax.loc = uu____48398;_},_e0::e1::e2::[])
          when
          (((let uu____48410 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48410 = "FStar.Buffer.rcreate_mm") ||
              (let uu____48415 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48415 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____48420 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48420 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____48425 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48425 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____48429 =
            let uu____48436 = translate_expr env e1  in
            let uu____48437 = translate_expr env e2  in
            (ManuallyManaged, uu____48436, uu____48437)  in
          EBufCreate uu____48429
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48439;
                  FStar_Extraction_ML_Syntax.loc = uu____48440;_},uu____48441);
             FStar_Extraction_ML_Syntax.mlty = uu____48442;
             FStar_Extraction_ML_Syntax.loc = uu____48443;_},_erid::elen::[])
          when
          let uu____48452 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48452 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____48456 =
            let uu____48461 = translate_expr env elen  in
            (ManuallyManaged, uu____48461)  in
          EBufCreateNoInit uu____48456
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48463;
                  FStar_Extraction_ML_Syntax.loc = uu____48464;_},uu____48465);
             FStar_Extraction_ML_Syntax.mlty = uu____48466;
             FStar_Extraction_ML_Syntax.loc = uu____48467;_},e2::[])
          when
          let uu____48475 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48475 = "FStar.HyperStack.ST.rfree" ->
          let uu____48479 = translate_expr env e2  in EBufFree uu____48479
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48481;
                  FStar_Extraction_ML_Syntax.loc = uu____48482;_},uu____48483);
             FStar_Extraction_ML_Syntax.mlty = uu____48484;
             FStar_Extraction_ML_Syntax.loc = uu____48485;_},e2::[])
          when
          (let uu____48495 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48495 = "FStar.Buffer.rfree") ||
            (let uu____48500 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48500 = "LowStar.Monotonic.Buffer.free")
          -> let uu____48504 = translate_expr env e2  in EBufFree uu____48504
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48506;
                  FStar_Extraction_ML_Syntax.loc = uu____48507;_},uu____48508);
             FStar_Extraction_ML_Syntax.mlty = uu____48509;
             FStar_Extraction_ML_Syntax.loc = uu____48510;_},e1::e2::_e3::[])
          when
          let uu____48520 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48520 = "FStar.Buffer.sub" ->
          let uu____48524 =
            let uu____48529 = translate_expr env e1  in
            let uu____48530 = translate_expr env e2  in
            (uu____48529, uu____48530)  in
          EBufSub uu____48524
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48532;
                  FStar_Extraction_ML_Syntax.loc = uu____48533;_},uu____48534);
             FStar_Extraction_ML_Syntax.mlty = uu____48535;
             FStar_Extraction_ML_Syntax.loc = uu____48536;_},e1::e2::_e3::[])
          when
          let uu____48546 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48546 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____48550 =
            let uu____48555 = translate_expr env e1  in
            let uu____48556 = translate_expr env e2  in
            (uu____48555, uu____48556)  in
          EBufSub uu____48550
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48558;
                  FStar_Extraction_ML_Syntax.loc = uu____48559;_},uu____48560);
             FStar_Extraction_ML_Syntax.mlty = uu____48561;
             FStar_Extraction_ML_Syntax.loc = uu____48562;_},e1::e2::[])
          when
          let uu____48571 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48571 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48576;
                  FStar_Extraction_ML_Syntax.loc = uu____48577;_},uu____48578);
             FStar_Extraction_ML_Syntax.mlty = uu____48579;
             FStar_Extraction_ML_Syntax.loc = uu____48580;_},e1::e2::[])
          when
          let uu____48589 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48589 = "FStar.Buffer.offset" ->
          let uu____48593 =
            let uu____48598 = translate_expr env e1  in
            let uu____48599 = translate_expr env e2  in
            (uu____48598, uu____48599)  in
          EBufSub uu____48593
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48601;
                  FStar_Extraction_ML_Syntax.loc = uu____48602;_},uu____48603);
             FStar_Extraction_ML_Syntax.mlty = uu____48604;
             FStar_Extraction_ML_Syntax.loc = uu____48605;_},e1::e2::[])
          when
          let uu____48614 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48614 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____48618 =
            let uu____48623 = translate_expr env e1  in
            let uu____48624 = translate_expr env e2  in
            (uu____48623, uu____48624)  in
          EBufSub uu____48618
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48626;
                  FStar_Extraction_ML_Syntax.loc = uu____48627;_},uu____48628);
             FStar_Extraction_ML_Syntax.mlty = uu____48629;
             FStar_Extraction_ML_Syntax.loc = uu____48630;_},e1::e2::e3::[])
          when
          (((let uu____48642 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48642 = "FStar.Buffer.upd") ||
              (let uu____48647 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48647 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____48652 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48652 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____48657 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48657 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____48661 =
            let uu____48668 = translate_expr env e1  in
            let uu____48669 = translate_expr env e2  in
            let uu____48670 = translate_expr env e3  in
            (uu____48668, uu____48669, uu____48670)  in
          EBufWrite uu____48661
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
             FStar_Extraction_ML_Syntax.loc = uu____48676;_},e1::e2::[])
          when
          let uu____48685 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48685 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____48689 =
            let uu____48696 = translate_expr env e1  in
            let uu____48697 = translate_expr env e2  in
            (uu____48696, (EConstant (UInt32, "0")), uu____48697)  in
          EBufWrite uu____48689
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____48701;
             FStar_Extraction_ML_Syntax.loc = uu____48702;_},uu____48703::[])
          when
          let uu____48706 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48706 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____48711;
             FStar_Extraction_ML_Syntax.loc = uu____48712;_},uu____48713::[])
          when
          let uu____48716 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48716 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48721;
                  FStar_Extraction_ML_Syntax.loc = uu____48722;_},uu____48723);
             FStar_Extraction_ML_Syntax.mlty = uu____48724;
             FStar_Extraction_ML_Syntax.loc = uu____48725;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____48739 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48739 = "FStar.Buffer.blit") ||
             (let uu____48744 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48744 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____48749 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48749 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____48753 =
            let uu____48764 = translate_expr env e1  in
            let uu____48765 = translate_expr env e2  in
            let uu____48766 = translate_expr env e3  in
            let uu____48767 = translate_expr env e4  in
            let uu____48768 = translate_expr env e5  in
            (uu____48764, uu____48765, uu____48766, uu____48767, uu____48768)
             in
          EBufBlit uu____48753
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48770;
                  FStar_Extraction_ML_Syntax.loc = uu____48771;_},uu____48772);
             FStar_Extraction_ML_Syntax.mlty = uu____48773;
             FStar_Extraction_ML_Syntax.loc = uu____48774;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____48790 =
            let uu____48797 = translate_expr env e1  in
            let uu____48798 = translate_expr env e2  in
            let uu____48799 = translate_expr env e3  in
            (uu____48797, uu____48798, uu____48799)  in
          EBufFill uu____48790
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____48801;
             FStar_Extraction_ML_Syntax.loc = uu____48802;_},uu____48803::[])
          when
          let uu____48806 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48806 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48811;
                  FStar_Extraction_ML_Syntax.loc = uu____48812;_},uu____48813);
             FStar_Extraction_ML_Syntax.mlty = uu____48814;
             FStar_Extraction_ML_Syntax.loc = uu____48815;_},_ebuf::_eseq::[])
          when
          (((let uu____48826 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48826 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____48831 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48831 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____48836 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48836 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____48841 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48841 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____48846;
             FStar_Extraction_ML_Syntax.loc = uu____48847;_},e1::[])
          when
          let uu____48851 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48851 = "Obj.repr" ->
          let uu____48855 =
            let uu____48860 = translate_expr env e1  in (uu____48860, TAny)
             in
          ECast uu____48855
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____48863;
             FStar_Extraction_ML_Syntax.loc = uu____48864;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____48880 = FStar_Util.must (mk_width m)  in
          let uu____48881 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____48880 uu____48881 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____48883;
             FStar_Extraction_ML_Syntax.loc = uu____48884;_},args)
          when is_bool_op op ->
          let uu____48898 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____48898 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____48900;
             FStar_Extraction_ML_Syntax.loc = uu____48901;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____48903;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____48904;_}::[])
          when is_machine_int m ->
          let uu____48929 =
            let uu____48935 = FStar_Util.must (mk_width m)  in
            (uu____48935, c)  in
          EConstant uu____48929
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____48938;
             FStar_Extraction_ML_Syntax.loc = uu____48939;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____48941;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____48942;_}::[])
          when is_machine_int m ->
          let uu____48967 =
            let uu____48973 = FStar_Util.must (mk_width m)  in
            (uu____48973, c)  in
          EConstant uu____48967
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____48975;
             FStar_Extraction_ML_Syntax.loc = uu____48976;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____48978;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____48979;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____48992 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____48994;
             FStar_Extraction_ML_Syntax.loc = uu____48995;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____48997;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____48998;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____49015 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49017;
             FStar_Extraction_ML_Syntax.loc = uu____49018;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49020;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49021;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____49036 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49038;
             FStar_Extraction_ML_Syntax.loc = uu____49039;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49041;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49042;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____49057 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____49060;
             FStar_Extraction_ML_Syntax.loc = uu____49061;_},arg::[])
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
            let uu____49089 =
              let uu____49094 = translate_expr env arg  in
              (uu____49094, (TInt UInt64))  in
            ECast uu____49089
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____49099 =
                 let uu____49104 = translate_expr env arg  in
                 (uu____49104, (TInt UInt32))  in
               ECast uu____49099)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____49109 =
                   let uu____49114 = translate_expr env arg  in
                   (uu____49114, (TInt UInt16))  in
                 ECast uu____49109)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____49119 =
                     let uu____49124 = translate_expr env arg  in
                     (uu____49124, (TInt UInt8))  in
                   ECast uu____49119)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____49129 =
                       let uu____49134 = translate_expr env arg  in
                       (uu____49134, (TInt Int64))  in
                     ECast uu____49129)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____49139 =
                         let uu____49144 = translate_expr env arg  in
                         (uu____49144, (TInt Int32))  in
                       ECast uu____49139)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____49149 =
                           let uu____49154 = translate_expr env arg  in
                           (uu____49154, (TInt Int16))  in
                         ECast uu____49149)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____49159 =
                             let uu____49164 = translate_expr env arg  in
                             (uu____49164, (TInt Int8))  in
                           ECast uu____49159)
                        else
                          (let uu____49167 =
                             let uu____49174 =
                               let uu____49177 = translate_expr env arg  in
                               [uu____49177]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____49174)
                              in
                           EApp uu____49167)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____49197 =
            let uu____49204 = translate_expr env head1  in
            let uu____49205 = FStar_List.map (translate_expr env) args  in
            (uu____49204, uu____49205)  in
          EApp uu____49197
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____49216 =
            let uu____49223 = translate_expr env head1  in
            let uu____49224 = FStar_List.map (translate_type env) ty_args  in
            (uu____49223, uu____49224)  in
          ETypApp uu____49216
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____49232 =
            let uu____49237 = translate_expr env e1  in
            let uu____49238 = translate_type env t_to  in
            (uu____49237, uu____49238)  in
          ECast uu____49232
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____49239,fields) ->
          let uu____49261 =
            let uu____49273 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____49274 =
              FStar_List.map
                (fun uu____49296  ->
                   match uu____49296 with
                   | (field,expr) ->
                       let uu____49311 = translate_expr env expr  in
                       (field, uu____49311)) fields
               in
            (uu____49273, uu____49274)  in
          EFlat uu____49261
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____49322 =
            let uu____49330 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____49331 = translate_expr env e1  in
            (uu____49330, uu____49331, (FStar_Pervasives_Native.snd path))
             in
          EField uu____49322
      | FStar_Extraction_ML_Syntax.MLE_Let uu____49337 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____49350) ->
          let uu____49355 =
            let uu____49357 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____49357
             in
          failwith uu____49355
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____49369 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____49369
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____49375 = FStar_List.map (translate_expr env) es  in
          ETuple uu____49375
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____49378,cons1),es) ->
          let uu____49393 =
            let uu____49403 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____49404 = FStar_List.map (translate_expr env) es  in
            (uu____49403, cons1, uu____49404)  in
          ECons uu____49393
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____49430 =
            let uu____49439 = translate_expr env1 body  in
            let uu____49440 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____49439, uu____49440)  in
          EFun uu____49430
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____49450 =
            let uu____49457 = translate_expr env e1  in
            let uu____49458 = translate_expr env e2  in
            let uu____49459 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____49457, uu____49458, uu____49459)  in
          EIfThenElse uu____49450
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____49461 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____49469 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____49485 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____49503 =
              let uu____49518 = FStar_List.map (translate_type env) ts  in
              (lid, uu____49518)  in
            TApp uu____49503
          else TQualified lid
      | uu____49533 -> failwith "invalid argument: assert_lid"

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
    fun uu____49560  ->
      match uu____49560 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____49587 = translate_pat env pat  in
            (match uu____49587 with
             | (env1,pat1) ->
                 let uu____49598 = translate_expr env1 expr  in
                 (pat1, uu____49598))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_49606  ->
    match uu___420_49606 with
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
          let uu____49673 =
            let uu____49674 =
              let uu____49680 = translate_width sw  in (uu____49680, s)  in
            PConstant uu____49674  in
          (env, uu____49673)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____49690,cons1),ps) ->
          let uu____49705 =
            FStar_List.fold_left
              (fun uu____49725  ->
                 fun p1  ->
                   match uu____49725 with
                   | (env1,acc) ->
                       let uu____49745 = translate_pat env1 p1  in
                       (match uu____49745 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____49705 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____49775,ps) ->
          let uu____49797 =
            FStar_List.fold_left
              (fun uu____49834  ->
                 fun uu____49835  ->
                   match (uu____49834, uu____49835) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____49915 = translate_pat env1 p1  in
                       (match uu____49915 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____49797 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____49986 =
            FStar_List.fold_left
              (fun uu____50006  ->
                 fun p1  ->
                   match uu____50006 with
                   | (env1,acc) ->
                       let uu____50026 = translate_pat env1 p1  in
                       (match uu____50026 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____49986 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____50053 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____50059 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____50073 =
            let uu____50075 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____50075
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____50073
          then
            let uu____50090 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____50090
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____50117) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____50135 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____50137 ->
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
          let uu____50161 =
            let uu____50168 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____50168)  in
          EApp uu____50161
