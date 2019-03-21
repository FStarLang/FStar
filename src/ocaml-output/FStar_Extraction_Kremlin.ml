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
    match projectee with | DGlobal _0 -> true | uu____42094 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____42205 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____42330 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____42437 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____42569 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____42686 -> false
  
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
    | uu____42827 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____42869 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____42880 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____42891 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____42902 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____42913 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____42924 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____42935 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____42946 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____42959 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____42980 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____42993 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____43016 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____43039 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____43060 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____43071 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____43082 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____43093 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____43104 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____43117 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____43147 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____43195 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____43228 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____43246 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____43289 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____43332 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____43375 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____43414 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____43443 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____43480 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____43521 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____43558 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____43599 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____43640 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____43699 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____43752 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____43787 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____43817 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____43828 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____43841 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____43862 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____43873 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____43885 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____43915 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____43974 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____44018 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____44055 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____44094 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____44128 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____44180 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____44218 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____44248 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____44292 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____44314 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____44337 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____44367 -> false
  
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____44378 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____44389 -> false
  
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____44400 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____44411 -> false
  
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____44422 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____44433 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____44444 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____44455 -> false
  
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BOr  -> true | uu____44466 -> false
  
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____44477 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____44488 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____44499 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____44510 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____44521 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____44532 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neq  -> true | uu____44543 -> false
  
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____44554 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lte  -> true | uu____44565 -> false
  
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____44576 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gte  -> true | uu____44587 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____44598 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____44609 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Xor  -> true | uu____44620 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____44631 -> false
  
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____44642 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____44655 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____44677 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____44703 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____44745 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____44777 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____44822 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____44855 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____44866 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____44877 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____44888 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____44899 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____44910 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____44921 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____44932 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____44943 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____44954 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____45003 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____45022 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____45040 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____45060 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____45102 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____45113 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____45129 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____45161 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____45197 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____45260 -> false
  
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
  'Auu____45361 'Auu____45362 'Auu____45363 .
    ('Auu____45361 * 'Auu____45362 * 'Auu____45363) -> 'Auu____45361
  =
  fun uu____45374  ->
    match uu____45374 with | (x,uu____45382,uu____45383) -> x
  
let snd3 :
  'Auu____45393 'Auu____45394 'Auu____45395 .
    ('Auu____45393 * 'Auu____45394 * 'Auu____45395) -> 'Auu____45394
  =
  fun uu____45406  ->
    match uu____45406 with | (uu____45413,x,uu____45415) -> x
  
let thd3 :
  'Auu____45425 'Auu____45426 'Auu____45427 .
    ('Auu____45425 * 'Auu____45426 * 'Auu____45427) -> 'Auu____45427
  =
  fun uu____45438  ->
    match uu____45438 with | (uu____45445,uu____45446,x) -> x
  
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___413_45456  ->
    match uu___413_45456 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____45468 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___414_45478  ->
    match uu___414_45478 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____45487 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___415_45508  ->
    match uu___415_45508 with
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
    | uu____45553 -> FStar_Pervasives_Native.None
  
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
      let uu___575_45709 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___575_45709.names_t);
        module_name = (uu___575_45709.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___579_45723 = env  in
      {
        names = (uu___579_45723.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___579_45723.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____45738 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____45738 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___590_45762  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___589_45769 ->
          let uu____45771 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____45771
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___599_45791  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___598_45800 ->
          let uu____45802 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____45802
  
let add_binders :
  'Auu____45813 . env -> (Prims.string * 'Auu____45813) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____45848  ->
             match uu____45848 with | (name,uu____45855) -> extend env1 name)
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
      | uu____45907 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____46126  ->
    match uu____46126 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____46175 = m  in
               match uu____46175 with
               | (path,uu____46190,uu____46191) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___641_46209  ->
                  match () with
                  | () ->
                      ((let uu____46213 =
                          let uu____46215 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____46215  in
                        if uu____46213
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____46221 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____46221))) ()
             with
             | e ->
                 ((let uu____46230 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____46230);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____46233  ->
    match uu____46233 with
    | (module_name,modul,uu____46248) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____46283 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___416_46297  ->
         match uu___416_46297 with
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
         | uu____46308 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____46312 =
      FStar_List.choose
        (fun uu___417_46319  ->
           match uu___417_46319 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____46326 -> FStar_Pervasives_Native.None) flags
       in
    match uu____46312 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____46339 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____46353 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____46355 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____46360) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____46387;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____46390;_} when
            FStar_Util.for_some
              (fun uu___418_46395  ->
                 match uu___418_46395 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____46398 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____46419 =
                let uu____46420 =
                  let uu____46441 = translate_cc meta  in
                  let uu____46444 = translate_flags meta  in
                  let uu____46447 = translate_type env t0  in
                  (uu____46441, uu____46444, name1, uu____46447)  in
                DExternal uu____46420  in
              FStar_Pervasives_Native.Some uu____46419
            else
              ((let uu____46463 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____46463);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____46469;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____46472;
                FStar_Extraction_ML_Syntax.loc = uu____46473;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____46475;_} ->
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
               let rec find_return_type eff i uu___419_46532 =
                 match uu___419_46532 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____46541,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____46561 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____46561 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____46587 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____46587
                         msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____46605) ->
                           let uu____46606 = translate_flags meta  in
                           MustDisappear :: uu____46606
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____46609 = translate_flags meta  in
                           MustDisappear :: uu____46609
                       | uu____46612 -> translate_flags meta  in
                     try
                       (fun uu___780_46621  ->
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
                         ((let uu____46653 =
                             let uu____46659 =
                               let uu____46661 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____46661 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____46659)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____46653);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____46687;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____46690;_} ->
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
                 (fun uu___807_46727  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____46751 =
                       let uu____46757 =
                         let uu____46759 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____46761 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n"
                           uu____46759 uu____46761
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____46757)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____46751);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____46779;
            FStar_Extraction_ML_Syntax.mllb_def = uu____46780;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____46781;
            FStar_Extraction_ML_Syntax.print_typ = uu____46782;_} ->
            ((let uu____46789 =
                let uu____46795 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____46795)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____46789);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____46802 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____46802
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____46816 = ty  in
      match uu____46816 with
      | (uu____46819,uu____46820,uu____46821,uu____46822,flags,uu____46824)
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
                     (let uu____46898 =
                        let uu____46899 =
                          let uu____46919 = translate_flags flags1  in
                          let uu____46922 = translate_type env1 t  in
                          (name1, uu____46919, (FStar_List.length args),
                            uu____46922)
                           in
                        DTypeAlias uu____46899  in
                      FStar_Pervasives_Native.Some uu____46898)
             | (uu____46935,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____46980 =
                   let uu____46981 =
                     let uu____47013 = translate_flags flags1  in
                     let uu____47016 =
                       FStar_List.map
                         (fun uu____47048  ->
                            match uu____47048 with
                            | (f,t) ->
                                let uu____47068 =
                                  let uu____47074 = translate_type env1 t  in
                                  (uu____47074, false)  in
                                (f, uu____47068)) fields
                        in
                     (name1, uu____47013, (FStar_List.length args),
                       uu____47016)
                      in
                   DTypeFlat uu____46981  in
                 FStar_Pervasives_Native.Some uu____46980
             | (uu____47107,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____47157 =
                   let uu____47158 =
                     let uu____47197 =
                       FStar_List.map
                         (fun uu____47250  ->
                            match uu____47250 with
                            | (cons1,ts) ->
                                let uu____47298 =
                                  FStar_List.map
                                    (fun uu____47330  ->
                                       match uu____47330 with
                                       | (name2,t) ->
                                           let uu____47350 =
                                             let uu____47356 =
                                               translate_type env1 t  in
                                             (uu____47356, false)  in
                                           (name2, uu____47350)) ts
                                   in
                                (cons1, uu____47298)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____47197)
                      in
                   DTypeVariant uu____47158  in
                 FStar_Pervasives_Native.Some uu____47157
             | (uu____47409,name,_mangled_name,uu____47412,uu____47413,uu____47414)
                 ->
                 ((let uu____47430 =
                     let uu____47436 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____47436)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____47430);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____47444 = find_t env name  in TBound uu____47444
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____47447,t2) ->
          let uu____47449 =
            let uu____47454 = translate_type env t1  in
            let uu____47455 = translate_type env t2  in
            (uu____47454, uu____47455)  in
          TArrow uu____47449
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____47459 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47459 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____47466 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47466 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____47483 = FStar_Util.must (mk_width m)  in TInt uu____47483
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____47497 = FStar_Util.must (mk_width m)  in TInt uu____47497
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____47502 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47502 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____47506::arg::uu____47508::[],p) when
          (((let uu____47514 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47514 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____47519 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____47519 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____47524 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____47524 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____47529 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47529 = "FStar.HyperStack.ST.s_mref")
          -> let uu____47533 = translate_type env arg  in TBuf uu____47533
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____47535::[],p) when
          ((((((((((let uu____47541 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____47541 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____47546 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____47546 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____47551 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____47551 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____47556 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____47556 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____47561 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____47561 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____47566 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____47566 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____47571 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____47571 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____47576 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____47576 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____47581 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____47581 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____47586 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____47586 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____47591 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47591 = "FStar.HyperStack.ST.mmmref")
          -> let uu____47595 = translate_type env arg  in TBuf uu____47595
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____47597::uu____47598::[],p) when
          let uu____47602 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47602 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____47606 = translate_type env arg  in TBuf uu____47606
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____47613 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____47613 = "FStar.Buffer.buffer") ||
                        (let uu____47618 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____47618 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____47623 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____47623 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____47628 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____47628 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____47633 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____47633 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____47638 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____47638 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____47643 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____47643 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____47648 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____47648 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____47653 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____47653 = "FStar.HyperStack.mmref"))
                ||
                (let uu____47658 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____47658 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____47663 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____47663 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____47668 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____47668 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____47673 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____47673 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____47678 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47678 = "FStar.HyperStack.ST.mmref")
          -> let uu____47682 = translate_type env arg  in TBuf uu____47682
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____47683::arg::[],p) when
          (let uu____47690 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____47690 = "FStar.HyperStack.s_ref") ||
            (let uu____47695 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____47695 = "FStar.HyperStack.ST.s_ref")
          -> let uu____47699 = translate_type env arg  in TBuf uu____47699
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____47700::[],p) when
          let uu____47704 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47704 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____47756 = FStar_List.map (translate_type env) args  in
          TTuple uu____47756
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____47767 =
              let uu____47782 = FStar_List.map (translate_type env) args  in
              (lid, uu____47782)  in
            TApp uu____47767
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____47800 = FStar_List.map (translate_type env) ts  in
          TTuple uu____47800

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
    fun uu____47818  ->
      match uu____47818 with
      | (name,typ) ->
          let uu____47828 = translate_type env typ  in
          { name; typ = uu____47828; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____47835 = find env name  in EBound uu____47835
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____47849 =
            let uu____47854 = FStar_Util.must (mk_op op)  in
            let uu____47855 = FStar_Util.must (mk_width m)  in
            (uu____47854, uu____47855)  in
          EOp uu____47849
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____47865 =
            let uu____47870 = FStar_Util.must (mk_bool_op op)  in
            (uu____47870, Bool)  in
          EOp uu____47865
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
            let uu____47893 = translate_type env typ  in
            { name; typ = uu____47893; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____47920 =
            let uu____47931 = translate_expr env expr  in
            let uu____47932 = translate_branches env branches  in
            (uu____47931, uu____47932)  in
          EMatch uu____47920
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____47946;
                  FStar_Extraction_ML_Syntax.loc = uu____47947;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____47949;
             FStar_Extraction_ML_Syntax.loc = uu____47950;_},arg::[])
          when
          let uu____47956 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47956 = "FStar.Dyn.undyn" ->
          let uu____47960 =
            let uu____47965 = translate_expr env arg  in
            let uu____47966 = translate_type env t  in
            (uu____47965, uu____47966)  in
          ECast uu____47960
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____47968;
                  FStar_Extraction_ML_Syntax.loc = uu____47969;_},uu____47970);
             FStar_Extraction_ML_Syntax.mlty = uu____47971;
             FStar_Extraction_ML_Syntax.loc = uu____47972;_},uu____47973)
          when
          let uu____47982 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____47982 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____47987;
                  FStar_Extraction_ML_Syntax.loc = uu____47988;_},uu____47989);
             FStar_Extraction_ML_Syntax.mlty = uu____47990;
             FStar_Extraction_ML_Syntax.loc = uu____47991;_},arg::[])
          when
          ((let uu____48001 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48001 = "FStar.HyperStack.All.failwith") ||
             (let uu____48006 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48006 = "FStar.Error.unexpected"))
            ||
            (let uu____48011 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48011 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____48016;
               FStar_Extraction_ML_Syntax.loc = uu____48017;_} -> EAbortS msg
           | uu____48019 ->
               let print7 =
                 let uu____48021 =
                   let uu____48022 =
                     let uu____48023 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____48023
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____48022  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____48021
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
                  FStar_Extraction_ML_Syntax.mlty = uu____48030;
                  FStar_Extraction_ML_Syntax.loc = uu____48031;_},uu____48032);
             FStar_Extraction_ML_Syntax.mlty = uu____48033;
             FStar_Extraction_ML_Syntax.loc = uu____48034;_},e1::[])
          when
          (let uu____48044 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48044 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____48049 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48049 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48054;
                  FStar_Extraction_ML_Syntax.loc = uu____48055;_},uu____48056);
             FStar_Extraction_ML_Syntax.mlty = uu____48057;
             FStar_Extraction_ML_Syntax.loc = uu____48058;_},e1::e2::[])
          when
          (((let uu____48069 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48069 = "FStar.Buffer.index") ||
              (let uu____48074 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48074 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____48079 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48079 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____48084 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48084 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____48088 =
            let uu____48093 = translate_expr env e1  in
            let uu____48094 = translate_expr env e2  in
            (uu____48093, uu____48094)  in
          EBufRead uu____48088
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48096;
                  FStar_Extraction_ML_Syntax.loc = uu____48097;_},uu____48098);
             FStar_Extraction_ML_Syntax.mlty = uu____48099;
             FStar_Extraction_ML_Syntax.loc = uu____48100;_},e1::[])
          when
          let uu____48108 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48108 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____48112 =
            let uu____48117 = translate_expr env e1  in
            (uu____48117, (EConstant (UInt32, "0")))  in
          EBufRead uu____48112
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48121;
                  FStar_Extraction_ML_Syntax.loc = uu____48122;_},uu____48123);
             FStar_Extraction_ML_Syntax.mlty = uu____48124;
             FStar_Extraction_ML_Syntax.loc = uu____48125;_},e1::e2::[])
          when
          ((let uu____48136 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48136 = "FStar.Buffer.create") ||
             (let uu____48141 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48141 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____48146 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48146 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____48150 =
            let uu____48157 = translate_expr env e1  in
            let uu____48158 = translate_expr env e2  in
            (Stack, uu____48157, uu____48158)  in
          EBufCreate uu____48150
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48160;
                  FStar_Extraction_ML_Syntax.loc = uu____48161;_},uu____48162);
             FStar_Extraction_ML_Syntax.mlty = uu____48163;
             FStar_Extraction_ML_Syntax.loc = uu____48164;_},elen::[])
          when
          let uu____48172 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48172 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____48176 =
            let uu____48181 = translate_expr env elen  in
            (Stack, uu____48181)  in
          EBufCreateNoInit uu____48176
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48183;
                  FStar_Extraction_ML_Syntax.loc = uu____48184;_},uu____48185);
             FStar_Extraction_ML_Syntax.mlty = uu____48186;
             FStar_Extraction_ML_Syntax.loc = uu____48187;_},init1::[])
          when
          let uu____48195 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48195 = "FStar.HyperStack.ST.salloc" ->
          let uu____48199 =
            let uu____48206 = translate_expr env init1  in
            (Stack, uu____48206, (EConstant (UInt32, "1")))  in
          EBufCreate uu____48199
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48210;
                  FStar_Extraction_ML_Syntax.loc = uu____48211;_},uu____48212);
             FStar_Extraction_ML_Syntax.mlty = uu____48213;
             FStar_Extraction_ML_Syntax.loc = uu____48214;_},e2::[])
          when
          ((let uu____48224 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48224 = "FStar.Buffer.createL") ||
             (let uu____48229 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48229 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____48234 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48234 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____48238 =
            let uu____48245 =
              let uu____48248 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____48248  in
            (Stack, uu____48245)  in
          EBufCreateL uu____48238
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48254;
                  FStar_Extraction_ML_Syntax.loc = uu____48255;_},uu____48256);
             FStar_Extraction_ML_Syntax.mlty = uu____48257;
             FStar_Extraction_ML_Syntax.loc = uu____48258;_},_erid::e2::[])
          when
          (let uu____48269 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48269 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____48274 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48274 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____48278 =
            let uu____48285 =
              let uu____48288 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____48288  in
            (Eternal, uu____48285)  in
          EBufCreateL uu____48278
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48294;
                  FStar_Extraction_ML_Syntax.loc = uu____48295;_},uu____48296);
             FStar_Extraction_ML_Syntax.mlty = uu____48297;
             FStar_Extraction_ML_Syntax.loc = uu____48298;_},_rid::init1::[])
          when
          let uu____48307 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48307 = "FStar.HyperStack.ST.ralloc" ->
          let uu____48311 =
            let uu____48318 = translate_expr env init1  in
            (Eternal, uu____48318, (EConstant (UInt32, "1")))  in
          EBufCreate uu____48311
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48322;
                  FStar_Extraction_ML_Syntax.loc = uu____48323;_},uu____48324);
             FStar_Extraction_ML_Syntax.mlty = uu____48325;
             FStar_Extraction_ML_Syntax.loc = uu____48326;_},_e0::e1::e2::[])
          when
          ((let uu____48338 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48338 = "FStar.Buffer.rcreate") ||
             (let uu____48343 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48343 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____48348 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48348 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____48352 =
            let uu____48359 = translate_expr env e1  in
            let uu____48360 = translate_expr env e2  in
            (Eternal, uu____48359, uu____48360)  in
          EBufCreate uu____48352
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48362;
                  FStar_Extraction_ML_Syntax.loc = uu____48363;_},uu____48364);
             FStar_Extraction_ML_Syntax.mlty = uu____48365;
             FStar_Extraction_ML_Syntax.loc = uu____48366;_},_erid::elen::[])
          when
          let uu____48375 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48375 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____48379 =
            let uu____48384 = translate_expr env elen  in
            (Eternal, uu____48384)  in
          EBufCreateNoInit uu____48379
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48386;
                  FStar_Extraction_ML_Syntax.loc = uu____48387;_},uu____48388);
             FStar_Extraction_ML_Syntax.mlty = uu____48389;
             FStar_Extraction_ML_Syntax.loc = uu____48390;_},_rid::init1::[])
          when
          let uu____48399 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48399 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____48403 =
            let uu____48410 = translate_expr env init1  in
            (ManuallyManaged, uu____48410, (EConstant (UInt32, "1")))  in
          EBufCreate uu____48403
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48414;
                  FStar_Extraction_ML_Syntax.loc = uu____48415;_},uu____48416);
             FStar_Extraction_ML_Syntax.mlty = uu____48417;
             FStar_Extraction_ML_Syntax.loc = uu____48418;_},_e0::e1::e2::[])
          when
          (((let uu____48430 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48430 = "FStar.Buffer.rcreate_mm") ||
              (let uu____48435 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48435 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____48440 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48440 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____48445 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48445 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____48449 =
            let uu____48456 = translate_expr env e1  in
            let uu____48457 = translate_expr env e2  in
            (ManuallyManaged, uu____48456, uu____48457)  in
          EBufCreate uu____48449
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48459;
                  FStar_Extraction_ML_Syntax.loc = uu____48460;_},uu____48461);
             FStar_Extraction_ML_Syntax.mlty = uu____48462;
             FStar_Extraction_ML_Syntax.loc = uu____48463;_},_erid::elen::[])
          when
          let uu____48472 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48472 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____48476 =
            let uu____48481 = translate_expr env elen  in
            (ManuallyManaged, uu____48481)  in
          EBufCreateNoInit uu____48476
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48483;
                  FStar_Extraction_ML_Syntax.loc = uu____48484;_},uu____48485);
             FStar_Extraction_ML_Syntax.mlty = uu____48486;
             FStar_Extraction_ML_Syntax.loc = uu____48487;_},e2::[])
          when
          let uu____48495 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48495 = "FStar.HyperStack.ST.rfree" ->
          let uu____48499 = translate_expr env e2  in EBufFree uu____48499
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48501;
                  FStar_Extraction_ML_Syntax.loc = uu____48502;_},uu____48503);
             FStar_Extraction_ML_Syntax.mlty = uu____48504;
             FStar_Extraction_ML_Syntax.loc = uu____48505;_},e2::[])
          when
          (let uu____48515 = FStar_Extraction_ML_Syntax.string_of_mlpath p
              in
           uu____48515 = "FStar.Buffer.rfree") ||
            (let uu____48520 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48520 = "LowStar.Monotonic.Buffer.free")
          -> let uu____48524 = translate_expr env e2  in EBufFree uu____48524
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48526;
                  FStar_Extraction_ML_Syntax.loc = uu____48527;_},uu____48528);
             FStar_Extraction_ML_Syntax.mlty = uu____48529;
             FStar_Extraction_ML_Syntax.loc = uu____48530;_},e1::e2::_e3::[])
          when
          let uu____48540 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48540 = "FStar.Buffer.sub" ->
          let uu____48544 =
            let uu____48549 = translate_expr env e1  in
            let uu____48550 = translate_expr env e2  in
            (uu____48549, uu____48550)  in
          EBufSub uu____48544
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48552;
                  FStar_Extraction_ML_Syntax.loc = uu____48553;_},uu____48554);
             FStar_Extraction_ML_Syntax.mlty = uu____48555;
             FStar_Extraction_ML_Syntax.loc = uu____48556;_},e1::e2::_e3::[])
          when
          let uu____48566 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48566 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____48570 =
            let uu____48575 = translate_expr env e1  in
            let uu____48576 = translate_expr env e2  in
            (uu____48575, uu____48576)  in
          EBufSub uu____48570
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48578;
                  FStar_Extraction_ML_Syntax.loc = uu____48579;_},uu____48580);
             FStar_Extraction_ML_Syntax.mlty = uu____48581;
             FStar_Extraction_ML_Syntax.loc = uu____48582;_},e1::e2::[])
          when
          let uu____48591 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48591 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48596;
                  FStar_Extraction_ML_Syntax.loc = uu____48597;_},uu____48598);
             FStar_Extraction_ML_Syntax.mlty = uu____48599;
             FStar_Extraction_ML_Syntax.loc = uu____48600;_},e1::e2::[])
          when
          let uu____48609 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48609 = "FStar.Buffer.offset" ->
          let uu____48613 =
            let uu____48618 = translate_expr env e1  in
            let uu____48619 = translate_expr env e2  in
            (uu____48618, uu____48619)  in
          EBufSub uu____48613
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48621;
                  FStar_Extraction_ML_Syntax.loc = uu____48622;_},uu____48623);
             FStar_Extraction_ML_Syntax.mlty = uu____48624;
             FStar_Extraction_ML_Syntax.loc = uu____48625;_},e1::e2::[])
          when
          let uu____48634 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48634 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____48638 =
            let uu____48643 = translate_expr env e1  in
            let uu____48644 = translate_expr env e2  in
            (uu____48643, uu____48644)  in
          EBufSub uu____48638
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48646;
                  FStar_Extraction_ML_Syntax.loc = uu____48647;_},uu____48648);
             FStar_Extraction_ML_Syntax.mlty = uu____48649;
             FStar_Extraction_ML_Syntax.loc = uu____48650;_},e1::e2::e3::[])
          when
          (((let uu____48662 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48662 = "FStar.Buffer.upd") ||
              (let uu____48667 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48667 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____48672 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48672 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____48677 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48677 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____48681 =
            let uu____48688 = translate_expr env e1  in
            let uu____48689 = translate_expr env e2  in
            let uu____48690 = translate_expr env e3  in
            (uu____48688, uu____48689, uu____48690)  in
          EBufWrite uu____48681
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48692;
                  FStar_Extraction_ML_Syntax.loc = uu____48693;_},uu____48694);
             FStar_Extraction_ML_Syntax.mlty = uu____48695;
             FStar_Extraction_ML_Syntax.loc = uu____48696;_},e1::e2::[])
          when
          let uu____48705 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48705 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____48709 =
            let uu____48716 = translate_expr env e1  in
            let uu____48717 = translate_expr env e2  in
            (uu____48716, (EConstant (UInt32, "0")), uu____48717)  in
          EBufWrite uu____48709
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____48721;
             FStar_Extraction_ML_Syntax.loc = uu____48722;_},uu____48723::[])
          when
          let uu____48726 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48726 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____48731;
             FStar_Extraction_ML_Syntax.loc = uu____48732;_},uu____48733::[])
          when
          let uu____48736 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48736 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48741;
                  FStar_Extraction_ML_Syntax.loc = uu____48742;_},uu____48743);
             FStar_Extraction_ML_Syntax.mlty = uu____48744;
             FStar_Extraction_ML_Syntax.loc = uu____48745;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____48759 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____48759 = "FStar.Buffer.blit") ||
             (let uu____48764 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48764 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____48769 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48769 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____48773 =
            let uu____48784 = translate_expr env e1  in
            let uu____48785 = translate_expr env e2  in
            let uu____48786 = translate_expr env e3  in
            let uu____48787 = translate_expr env e4  in
            let uu____48788 = translate_expr env e5  in
            (uu____48784, uu____48785, uu____48786, uu____48787, uu____48788)
             in
          EBufBlit uu____48773
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48790;
                  FStar_Extraction_ML_Syntax.loc = uu____48791;_},uu____48792);
             FStar_Extraction_ML_Syntax.mlty = uu____48793;
             FStar_Extraction_ML_Syntax.loc = uu____48794;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____48810 =
            let uu____48817 = translate_expr env e1  in
            let uu____48818 = translate_expr env e2  in
            let uu____48819 = translate_expr env e3  in
            (uu____48817, uu____48818, uu____48819)  in
          EBufFill uu____48810
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____48821;
             FStar_Extraction_ML_Syntax.loc = uu____48822;_},uu____48823::[])
          when
          let uu____48826 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48826 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____48831;
                  FStar_Extraction_ML_Syntax.loc = uu____48832;_},uu____48833);
             FStar_Extraction_ML_Syntax.mlty = uu____48834;
             FStar_Extraction_ML_Syntax.loc = uu____48835;_},_ebuf::_eseq::[])
          when
          (((let uu____48846 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48846 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____48851 =
                 FStar_Extraction_ML_Syntax.string_of_mlpath p  in
               uu____48851 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____48856 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____48856 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____48861 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____48861 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____48866;
             FStar_Extraction_ML_Syntax.loc = uu____48867;_},e1::[])
          when
          let uu____48871 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____48871 = "Obj.repr" ->
          let uu____48875 =
            let uu____48880 = translate_expr env e1  in (uu____48880, TAny)
             in
          ECast uu____48875
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____48883;
             FStar_Extraction_ML_Syntax.loc = uu____48884;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____48900 = FStar_Util.must (mk_width m)  in
          let uu____48901 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____48900 uu____48901 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____48903;
             FStar_Extraction_ML_Syntax.loc = uu____48904;_},args)
          when is_bool_op op ->
          let uu____48918 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____48918 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____48920;
             FStar_Extraction_ML_Syntax.loc = uu____48921;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____48923;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____48924;_}::[])
          when is_machine_int m ->
          let uu____48949 =
            let uu____48955 = FStar_Util.must (mk_width m)  in
            (uu____48955, c)  in
          EConstant uu____48949
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____48958;
             FStar_Extraction_ML_Syntax.loc = uu____48959;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 =
                                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                                 (FStar_Extraction_ML_Syntax.MLC_Int
                                                                 (c,FStar_Pervasives_Native.None
                                                                  ));
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____48961;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____48962;_}::[])
          when is_machine_int m ->
          let uu____48987 =
            let uu____48993 = FStar_Util.must (mk_width m)  in
            (uu____48993, c)  in
          EConstant uu____48987
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____48995;
             FStar_Extraction_ML_Syntax.loc = uu____48996;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____48998;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____48999;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____49012 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49014;
             FStar_Extraction_ML_Syntax.loc = uu____49015;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49017;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49018;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____49035 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49037;
             FStar_Extraction_ML_Syntax.loc = uu____49038;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49040;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49041;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____49056 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____49058;
             FStar_Extraction_ML_Syntax.loc = uu____49059;_},{
                                                               FStar_Extraction_ML_Syntax.expr
                                                                 = e1;
                                                               FStar_Extraction_ML_Syntax.mlty
                                                                 =
                                                                 uu____49061;
                                                               FStar_Extraction_ML_Syntax.loc
                                                                 =
                                                                 uu____49062;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____49077 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____49080;
             FStar_Extraction_ML_Syntax.loc = uu____49081;_},arg::[])
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
            let uu____49109 =
              let uu____49114 = translate_expr env arg  in
              (uu____49114, (TInt UInt64))  in
            ECast uu____49109
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____49119 =
                 let uu____49124 = translate_expr env arg  in
                 (uu____49124, (TInt UInt32))  in
               ECast uu____49119)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____49129 =
                   let uu____49134 = translate_expr env arg  in
                   (uu____49134, (TInt UInt16))  in
                 ECast uu____49129)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____49139 =
                     let uu____49144 = translate_expr env arg  in
                     (uu____49144, (TInt UInt8))  in
                   ECast uu____49139)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____49149 =
                       let uu____49154 = translate_expr env arg  in
                       (uu____49154, (TInt Int64))  in
                     ECast uu____49149)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____49159 =
                         let uu____49164 = translate_expr env arg  in
                         (uu____49164, (TInt Int32))  in
                       ECast uu____49159)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____49169 =
                           let uu____49174 = translate_expr env arg  in
                           (uu____49174, (TInt Int16))  in
                         ECast uu____49169)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____49179 =
                             let uu____49184 = translate_expr env arg  in
                             (uu____49184, (TInt Int8))  in
                           ECast uu____49179)
                        else
                          (let uu____49187 =
                             let uu____49194 =
                               let uu____49197 = translate_expr env arg  in
                               [uu____49197]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____49194)
                              in
                           EApp uu____49187)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____49217 =
            let uu____49224 = translate_expr env head1  in
            let uu____49225 = FStar_List.map (translate_expr env) args  in
            (uu____49224, uu____49225)  in
          EApp uu____49217
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____49236 =
            let uu____49243 = translate_expr env head1  in
            let uu____49244 = FStar_List.map (translate_type env) ty_args  in
            (uu____49243, uu____49244)  in
          ETypApp uu____49236
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____49252 =
            let uu____49257 = translate_expr env e1  in
            let uu____49258 = translate_type env t_to  in
            (uu____49257, uu____49258)  in
          ECast uu____49252
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____49259,fields) ->
          let uu____49281 =
            let uu____49293 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____49294 =
              FStar_List.map
                (fun uu____49316  ->
                   match uu____49316 with
                   | (field,expr) ->
                       let uu____49331 = translate_expr env expr  in
                       (field, uu____49331)) fields
               in
            (uu____49293, uu____49294)  in
          EFlat uu____49281
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____49342 =
            let uu____49350 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____49351 = translate_expr env e1  in
            (uu____49350, uu____49351, (FStar_Pervasives_Native.snd path))
             in
          EField uu____49342
      | FStar_Extraction_ML_Syntax.MLE_Let uu____49357 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____49370) ->
          let uu____49375 =
            let uu____49377 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____49377
             in
          failwith uu____49375
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____49389 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____49389
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____49395 = FStar_List.map (translate_expr env) es  in
          ETuple uu____49395
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____49398,cons1),es) ->
          let uu____49413 =
            let uu____49423 =
              assert_lid env e.FStar_Extraction_ML_Syntax.mlty  in
            let uu____49424 = FStar_List.map (translate_expr env) es  in
            (uu____49423, cons1, uu____49424)  in
          ECons uu____49413
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____49450 =
            let uu____49459 = translate_expr env1 body  in
            let uu____49460 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____49459, uu____49460)  in
          EFun uu____49450
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____49470 =
            let uu____49477 = translate_expr env e1  in
            let uu____49478 = translate_expr env e2  in
            let uu____49479 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____49477, uu____49478, uu____49479)  in
          EIfThenElse uu____49470
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____49481 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____49489 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____49505 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____49523 =
              let uu____49538 = FStar_List.map (translate_type env) ts  in
              (lid, uu____49538)  in
            TApp uu____49523
          else TQualified lid
      | uu____49553 -> failwith "invalid argument: assert_lid"

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
    fun uu____49580  ->
      match uu____49580 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____49607 = translate_pat env pat  in
            (match uu____49607 with
             | (env1,pat1) ->
                 let uu____49618 = translate_expr env1 expr  in
                 (pat1, uu____49618))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___420_49626  ->
    match uu___420_49626 with
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
          let uu____49693 =
            let uu____49694 =
              let uu____49700 = translate_width sw  in (uu____49700, s)  in
            PConstant uu____49694  in
          (env, uu____49693)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____49710,cons1),ps) ->
          let uu____49725 =
            FStar_List.fold_left
              (fun uu____49745  ->
                 fun p1  ->
                   match uu____49745 with
                   | (env1,acc) ->
                       let uu____49765 = translate_pat env1 p1  in
                       (match uu____49765 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____49725 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____49795,ps) ->
          let uu____49817 =
            FStar_List.fold_left
              (fun uu____49854  ->
                 fun uu____49855  ->
                   match (uu____49854, uu____49855) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____49935 = translate_pat env1 p1  in
                       (match uu____49935 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____49817 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____50006 =
            FStar_List.fold_left
              (fun uu____50026  ->
                 fun p1  ->
                   match uu____50026 with
                   | (env1,acc) ->
                       let uu____50046 = translate_pat env1 p1  in
                       (match uu____50046 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____50006 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____50073 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____50079 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____50093 =
            let uu____50095 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____50095
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____50093
          then
            let uu____50110 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____50110
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____50137) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____50155 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____50157 ->
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
          let uu____50181 =
            let uu____50188 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____50188)  in
          EApp uu____50181
