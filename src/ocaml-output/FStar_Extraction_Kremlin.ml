open Prims
type decl =
  | DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) *
  typ * expr) 
  | DFunction of (cc Prims.option * flag Prims.list * Prims.int * typ *
  (Prims.string Prims.list * Prims.string) * binder Prims.list * expr) 
  | DTypeAlias of ((Prims.string Prims.list * Prims.string) * Prims.int *
  typ) 
  | DTypeFlat of ((Prims.string Prims.list * Prims.string) * Prims.int *
  (Prims.string * (typ * Prims.bool)) Prims.list) 
  | DExternal of (cc Prims.option * (Prims.string Prims.list * Prims.string)
  * typ) 
  | DTypeVariant of ((Prims.string Prims.list * Prims.string) * Prims.int *
  (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list) 
and cc =
  | StdCall 
  | CDecl 
  | FastCall 
and flag =
  | Private 
  | NoExtract 
  | CInline 
  | Substitute 
and lifetime =
  | Eternal 
  | Stack 
and expr =
  | EBound of Prims.int 
  | EQualified of (Prims.string Prims.list * Prims.string) 
  | EConstant of (width * Prims.string) 
  | EUnit 
  | EApp of (expr * expr Prims.list) 
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
  | EFun of (binder Prims.list * expr) 
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
  | Int 
  | UInt 
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
  | TZ 
  | TBound of Prims.int 
  | TApp of ((Prims.string Prims.list * Prims.string) * typ Prims.list) 
  | TTuple of typ Prims.list 
let uu___is_DGlobal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____300 -> false
  
let __proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * typ * expr)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let uu___is_DFunction : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____349 -> false
  
let __proj__DFunction__item___0 :
  decl ->
    (cc Prims.option * flag Prims.list * Prims.int * typ * (Prims.string
      Prims.list * Prims.string) * binder Prims.list * expr)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let uu___is_DTypeAlias : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____406 -> false
  
let __proj__DTypeAlias__item___0 :
  decl -> ((Prims.string Prims.list * Prims.string) * Prims.int * typ) =
  fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let uu___is_DTypeFlat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____447 -> false
  
let __proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string *
      (typ * Prims.bool)) Prims.list)
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let uu___is_DExternal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____499 -> false
  
let __proj__DExternal__item___0 :
  decl -> (cc Prims.option * (Prims.string Prims.list * Prims.string) * typ)
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let uu___is_DTypeVariant : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____546 -> false
  
let __proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string *
      (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list)
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let uu___is_StdCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____599 -> false
  
let uu___is_CDecl : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____603 -> false
  
let uu___is_FastCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____607 -> false
  
let uu___is_Private : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____611 -> false
  
let uu___is_NoExtract : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____615 -> false
  
let uu___is_CInline : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____619 -> false
  
let uu___is_Substitute : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____623 -> false
  
let uu___is_Eternal : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____627 -> false
  
let uu___is_Stack : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____631 -> false
  
let uu___is_EBound : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____636 -> false
  
let __proj__EBound__item___0 : expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let uu___is_EQualified : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____651 -> false
  
let __proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let uu___is_EConstant : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____674 -> false
  
let __proj__EConstant__item___0 : expr -> (width * Prims.string) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let uu___is_EUnit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____691 -> false
  
let uu___is_EApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____699 -> false
  
let __proj__EApp__item___0 : expr -> (expr * expr Prims.list) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let uu___is_ELet : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____723 -> false
  
let __proj__ELet__item___0 : expr -> (binder * expr * expr) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let uu___is_EIfThenElse : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____747 -> false
  
let __proj__EIfThenElse__item___0 : expr -> (expr * expr * expr) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let uu___is_ESequence : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____769 -> false
  
let __proj__ESequence__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let uu___is_EAssign : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____786 -> false
  
let __proj__EAssign__item___0 : expr -> (expr * expr) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let uu___is_EBufCreate : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____807 -> false
  
let __proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let uu___is_EBufRead : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____830 -> false
  
let __proj__EBufRead__item___0 : expr -> (expr * expr) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let uu___is_EBufWrite : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____851 -> false
  
let __proj__EBufWrite__item___0 : expr -> (expr * expr * expr) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let uu___is_EBufSub : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____874 -> false
  
let __proj__EBufSub__item___0 : expr -> (expr * expr) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let uu___is_EBufBlit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____897 -> false
  
let __proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let uu___is_EMatch : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____929 -> false
  
let __proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list) =
  fun projectee  -> match projectee with | EMatch _0 -> _0 
let uu___is_EOp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____958 -> false
  
let __proj__EOp__item___0 : expr -> (op * width) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let uu___is_ECast : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____978 -> false
  
let __proj__ECast__item___0 : expr -> (expr * typ) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let uu___is_EPushFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____995 -> false
  
let uu___is_EPopFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____999 -> false
  
let uu___is_EBool : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1004 -> false
  
let __proj__EBool__item___0 : expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let uu___is_EAny : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1015 -> false
  
let uu___is_EAbort : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1019 -> false
  
let uu___is_EReturn : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1024 -> false
  
let __proj__EReturn__item___0 : expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let uu___is_EFlat : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1041 -> false
  
let __proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let uu___is_EField : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1071 -> false
  
let __proj__EField__item___0 : expr -> (typ * expr * Prims.string) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let uu___is_EWhile : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1094 -> false
  
let __proj__EWhile__item___0 : expr -> (expr * expr) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let uu___is_EBufCreateL : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1115 -> false
  
let __proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let uu___is_ETuple : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1137 -> false
  
let __proj__ETuple__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let uu___is_ECons : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1156 -> false
  
let __proj__ECons__item___0 : expr -> (typ * Prims.string * expr Prims.list)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let uu___is_EBufFill : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____1183 -> false
  
let __proj__EBufFill__item___0 : expr -> (expr * expr * expr) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let uu___is_EString : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____1204 -> false
  
let __proj__EString__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0 
let uu___is_EFun : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____1219 -> false
  
let __proj__EFun__item___0 : expr -> (binder Prims.list * expr) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____1239 -> false 
let uu___is_AddW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____1243 -> false
  
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____1247 -> false 
let uu___is_SubW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____1251 -> false
  
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____1255 -> false 
let uu___is_DivW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____1259 -> false
  
let uu___is_Mult : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____1263 -> false
  
let uu___is_MultW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____1267 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____1271 -> false 
let uu___is_BOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____1275 -> false 
let uu___is_BAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____1279 -> false
  
let uu___is_BXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____1283 -> false
  
let uu___is_BShiftL : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____1287 -> false
  
let uu___is_BShiftR : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____1291 -> false
  
let uu___is_BNot : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____1295 -> false
  
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____1299 -> false 
let uu___is_Neq : op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____1303 -> false 
let uu___is_Lt : op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____1307 -> false 
let uu___is_Lte : op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____1311 -> false 
let uu___is_Gt : op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____1315 -> false 
let uu___is_Gte : op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____1319 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____1323 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____1327 -> false 
let uu___is_Xor : op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____1331 -> false 
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____1335 -> false 
let uu___is_PUnit : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____1339 -> false
  
let uu___is_PBool : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____1344 -> false
  
let __proj__PBool__item___0 : pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let uu___is_PVar : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____1356 -> false
  
let __proj__PVar__item___0 : pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let uu___is_PCons : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____1371 -> false
  
let __proj__PCons__item___0 : pattern -> (Prims.string * pattern Prims.list)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let uu___is_PTuple : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____1393 -> false
  
let __proj__PTuple__item___0 : pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let uu___is_PRecord : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____1411 -> false
  
let __proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let uu___is_UInt8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____1431 -> false
  
let uu___is_UInt16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____1435 -> false
  
let uu___is_UInt32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____1439 -> false
  
let uu___is_UInt64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____1443 -> false
  
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____1447 -> false
  
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____1451 -> false
  
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____1455 -> false
  
let uu___is_Int64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____1459 -> false
  
let uu___is_Bool : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____1463 -> false
  
let uu___is_Int : width -> Prims.bool =
  fun projectee  -> match projectee with | Int  -> true | uu____1467 -> false 
let uu___is_UInt : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt  -> true | uu____1471 -> false
  
let uu___is_TInt : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____1488 -> false
  
let __proj__TInt__item___0 : typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let uu___is_TBuf : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____1500 -> false
  
let __proj__TBuf__item___0 : typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let uu___is_TUnit : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____1511 -> false
  
let uu___is_TQualified : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____1519 -> false
  
let __proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let uu___is_TBool : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____1539 -> false
  
let uu___is_TAny : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____1543 -> false
  
let uu___is_TArrow : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____1550 -> false
  
let __proj__TArrow__item___0 : typ -> (typ * typ) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let uu___is_TZ : typ -> Prims.bool =
  fun projectee  -> match projectee with | TZ  -> true | uu____1567 -> false 
let uu___is_TBound : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____1572 -> false
  
let __proj__TBound__item___0 : typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let uu___is_TApp : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____1590 -> false
  
let __proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let uu___is_TTuple : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____1621 -> false
  
let __proj__TTuple__item___0 : typ -> typ Prims.list =
  fun projectee  -> match projectee with | TTuple _0 -> _0 
type program = decl Prims.list
type ident = Prims.string
type fields_t = (Prims.string * (typ * Prims.bool)) Prims.list
type branches_t =
  (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list
type branch = (pattern * expr)
type branches = (pattern * expr) Prims.list
type constant = (width * Prims.string)
type var = Prims.int
type lident = (Prims.string Prims.list * Prims.string)
type version = Prims.int
let current_version : Prims.int = (Prims.parse_int "20") 
type file = (Prims.string * program)
type binary_format = (version * file Prims.list)
let fst3 uu____1674 = match uu____1674 with | (x,uu____1679,uu____1680) -> x 
let snd3 uu____1694 = match uu____1694 with | (uu____1698,x,uu____1700) -> x 
let thd3 uu____1714 = match uu____1714 with | (uu____1718,uu____1719,x) -> x 
let mk_width : Prims.string -> width Prims.option =
  fun uu___115_1724  ->
    match uu___115_1724 with
    | "UInt8" -> Some UInt8
    | "UInt16" -> Some UInt16
    | "UInt32" -> Some UInt32
    | "UInt64" -> Some UInt64
    | "Int8" -> Some Int8
    | "Int16" -> Some Int16
    | "Int32" -> Some Int32
    | "Int64" -> Some Int64
    | uu____1726 -> None
  
let mk_bool_op : Prims.string -> op Prims.option =
  fun uu___116_1730  ->
    match uu___116_1730 with
    | "op_Negation" -> Some Not
    | "op_AmpAmp" -> Some And
    | "op_BarBar" -> Some Or
    | "op_Equality" -> Some Eq
    | "op_disEquality" -> Some Neq
    | uu____1732 -> None
  
let is_bool_op : Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> None 
let mk_op : Prims.string -> op Prims.option =
  fun uu___117_1740  ->
    match uu___117_1740 with
    | "add"|"op_Plus_Hat" -> Some Add
    | "add_mod"|"op_Plus_Percent_Hat" -> Some AddW
    | "sub"|"op_Subtraction_Hat" -> Some Sub
    | "sub_mod"|"op_Subtraction_Percent_Hat" -> Some SubW
    | "mul"|"op_Star_Hat" -> Some Mult
    | "mul_mod"|"op_Star_Percent_Hat" -> Some MultW
    | "div"|"op_Slash_Hat" -> Some Div
    | "div_mod"|"op_Slash_Percent_Hat" -> Some DivW
    | "rem"|"op_Percent_Hat" -> Some Mod
    | "logor"|"op_Bar_Hat" -> Some BOr
    | "logxor"|"op_Hat_Hat" -> Some BXor
    | "logand"|"op_Amp_Hat" -> Some BAnd
    | "lognot" -> Some BNot
    | "shift_right"|"op_Greater_Greater_Hat" -> Some BShiftR
    | "shift_left"|"op_Less_Less_Hat" -> Some BShiftL
    | "eq"|"op_Equals_Hat" -> Some Eq
    | "op_Greater_Hat"|"gt" -> Some Gt
    | "op_Greater_Equals_Hat"|"gte" -> Some Gte
    | "op_Less_Hat"|"lt" -> Some Lt
    | "op_Less_Equals_Hat"|"lte" -> Some Lte
    | uu____1742 -> None
  
let is_op : Prims.string -> Prims.bool = fun op  -> (mk_op op) <> None 
let is_machine_int : Prims.string -> Prims.bool =
  fun m  -> (mk_width m) <> None 
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }
and name = {
  pretty: Prims.string ;
  mut: Prims.bool }
let empty : Prims.string Prims.list -> env =
  fun module_name  -> { names = []; names_t = []; module_name } 
let extend : env -> Prims.string -> Prims.bool -> env =
  fun env  ->
    fun x  ->
      fun is_mut  ->
        let uu___122_1809 = env  in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___122_1809.names_t);
          module_name = (uu___122_1809.module_name)
        }
  
let extend_t : env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___123_1816 = env  in
      {
        names = (uu___123_1816.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___123_1816.module_name)
      }
  
let find_name : env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____1823 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____1823 with
      | Some name -> name
      | None  -> failwith "internal error: name not found"
  
let is_mutable : env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> (find_name env x).mut 
let find : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____1842 ->
          failwith
            (FStar_Util.format1 "Internal error: name not found %s\n" x)
  
let find_t : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____1852 ->
          failwith
            (FStar_Util.format1 "Internal error: name not found %s\n" x)
  
let add_binders env binders =
  FStar_List.fold_left
    (fun env  ->
       fun uu____1882  ->
         match uu____1882 with
         | ((name,uu____1888),uu____1889) -> extend env name false) env
    binders
  
let rec translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____1980  ->
    match uu____1980 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____2011 = m  in
               match uu____2011 with
               | ((prefix,final),uu____2023,uu____2024) ->
                   FStar_String.concat "." (FStar_List.append prefix [final])
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               Some (translate_module m)
             with
             | e ->
                 ((let _0_366 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     _0_366);
                  None)) modules

and translate_module :
  ((Prims.string Prims.list * Prims.string) *
    (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule)
    Prims.option * FStar_Extraction_ML_Syntax.mllib) -> file
  =
  fun uu____2044  ->
    match uu____2044 with
    | (module_name,modul,uu____2056) ->
        let module_name =
          FStar_List.append (Prims.fst module_name) [Prims.snd module_name]
           in
        let program =
          match modul with
          | Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name))
                decls
          | uu____2080 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name), program)

and translate_flags :
  FStar_Extraction_ML_Syntax.c_flag Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___118_2088  ->
         match uu___118_2088 with
         | FStar_Extraction_ML_Syntax.Private  -> Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  -> Some NoExtract
         | FStar_Extraction_ML_Syntax.Attribute "c_inline" -> Some CInline
         | FStar_Extraction_ML_Syntax.Attribute "substitute" ->
             Some Substitute
         | FStar_Extraction_ML_Syntax.Attribute a ->
             (FStar_Util.print1_warning "Warning: unrecognized attribute %s"
                a;
              None)
         | uu____2092 -> None) flags

and translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.option =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
        (flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = (name,_);
                        FStar_Extraction_ML_Syntax.mllb_tysc = Some
                          (tvars,t0);
                        FStar_Extraction_ML_Syntax.mllb_add_unit = _;
                        FStar_Extraction_ML_Syntax.mllb_def =
                          {
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                            FStar_Extraction_ML_Syntax.mlty = _;
                            FStar_Extraction_ML_Syntax.loc = _;_};
                        FStar_Extraction_ML_Syntax.print_typ = _;_}::[])
        |FStar_Extraction_ML_Syntax.MLM_Let
        (flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = (name,_);
                        FStar_Extraction_ML_Syntax.mllb_tysc = Some
                          (tvars,t0);
                        FStar_Extraction_ML_Syntax.mllb_add_unit = _;
                        FStar_Extraction_ML_Syntax.mllb_def =
                          {
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Coerce
                              ({
                                 FStar_Extraction_ML_Syntax.expr =
                                   FStar_Extraction_ML_Syntax.MLE_Fun
                                   (args,body);
                                 FStar_Extraction_ML_Syntax.mlty = _;
                                 FStar_Extraction_ML_Syntax.loc = _;_},_,_);
                            FStar_Extraction_ML_Syntax.mlty = _;
                            FStar_Extraction_ML_Syntax.loc = _;_};
                        FStar_Extraction_ML_Syntax.print_typ = _;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___119_2137  ->
                 match uu___119_2137 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2138 -> false) flags
             in
          let env =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2145  ->
                   match uu____2145 with
                   | (name,uu____2149) -> extend_t env name) env tvars
             in
          let rec find_return_type uu___120_2153 =
            match uu___120_2153 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2154,uu____2155,t)
                -> find_return_type t
            | t -> t  in
          let t =
            let _0_367 = find_return_type t0  in translate_type env _0_367
             in
          let binders = translate_binders env args  in
          let env = add_binders env args  in
          let name = ((env.module_name), name)  in
          let flags = translate_flags flags  in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               Some
                 (DExternal
                    (let _0_368 = translate_type env t0  in
                     (None, name, _0_368)))
             else None)
          else
            (try
               let body = translate_expr env body  in
               Some
                 (DFunction
                    (None, flags, (FStar_List.length tvars), t, name,
                      binders, body))
             with
             | e ->
                 ((let _0_369 = FStar_Util.print_exn e  in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (Prims.snd name) _0_369);
                  Some
                    (DFunction
                       (None, flags, (FStar_List.length tvars), t, name,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2207);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2209;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2211;_}::[])
          ->
          let flags = translate_flags flags  in
          let t = translate_type env t  in
          let name = ((env.module_name), name)  in
          (try
             let expr = translate_expr env expr  in
             Some (DGlobal (flags, name, t, expr))
           with
           | e ->
               ((let _0_370 = FStar_Util.print_exn e  in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (Prims.snd name) _0_370);
                Some (DGlobal (flags, name, t, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____2242,uu____2243,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____2245);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____2247;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____2248;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____2249;_}::uu____2250)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | Some (idents,t) ->
                let _0_373 =
                  let _0_371 = FStar_List.map Prims.fst idents  in
                  FStar_String.concat ", " _0_371  in
                let _0_372 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n" _0_373
                  _0_372
            | None  -> ());
           None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____2263 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____2265 -> None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2297  ->
                   match uu____2297 with
                   | (name,uu____2301) -> extend_t env name) env args
             in
          if assumed
          then None
          else
            Some
              (DTypeAlias
                 ((let _0_374 = translate_type env t  in
                   (name, (FStar_List.length args), _0_374))))
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2309,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2343  ->
                   match uu____2343 with
                   | (name,uu____2347) -> extend_t env name) env args
             in
          Some
            (DTypeFlat
               (let _0_377 =
                  FStar_List.map
                    (fun uu____2364  ->
                       match uu____2364 with
                       | (f,t) ->
                           let _0_376 =
                             let _0_375 = translate_type env t  in
                             (_0_375, false)  in
                           (f, _0_376)) fields
                   in
                (name, (FStar_List.length args), _0_377)))
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2375,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2410  ->
                   match uu____2410 with
                   | (name,uu____2414) -> extend_t env name) env args
             in
          Some
            (DTypeVariant
               (let _0_384 =
                  FStar_List.mapi
                    (fun i  ->
                       fun uu____2439  ->
                         match uu____2439 with
                         | (cons,ts) ->
                             let _0_383 =
                               FStar_List.mapi
                                 (fun j  ->
                                    fun t  ->
                                      let _0_382 =
                                        let _0_379 =
                                          FStar_Util.string_of_int i  in
                                        let _0_378 =
                                          FStar_Util.string_of_int j  in
                                        FStar_Util.format2 "x%s%s" _0_379
                                          _0_378
                                         in
                                      let _0_381 =
                                        let _0_380 = translate_type env t  in
                                        (_0_380, false)  in
                                      (_0_382, _0_381)) ts
                                in
                             (cons, _0_383)) branches
                   in
                (name, (FStar_List.length args), _0_384)))
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2467,name,_mangled_name,uu____2470,uu____2471)::uu____2472)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2494 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2496 ->
          failwith "todo: translate_decl [MLM_Exn]"

and translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple []
        |FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____2504) ->
          TBound (find_t env name)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2506,t2) ->
          TArrow
            (let _0_386 = translate_type env t1  in
             let _0_385 = translate_type env t2  in (_0_386, _0_385))
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let _0_387 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_387 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let _0_388 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_388 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m -> TInt (FStar_Util.must (mk_width m))
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m -> TInt (FStar_Util.must (mk_width m))
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let _0_389 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_389 = "FStar.Buffer.buffer" -> TBuf (translate_type env arg)
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2527::[],p) when
          let _0_390 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_390 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,("Prims"::[],t)) when
          FStar_Util.starts_with t "tuple" ->
          TTuple (FStar_List.map (translate_type env) args)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            TApp
              (let _0_391 = FStar_List.map (translate_type env) args  in
               (lid, _0_391))
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          TTuple (FStar_List.map (translate_type env) ts)

and translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
      Prims.list -> binder Prims.list
  = fun env  -> fun args  -> FStar_List.map (translate_binder env) args

and translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) ->
      binder
  =
  fun env  ->
    fun uu____2566  ->
      match uu____2566 with
      | ((name,uu____2570),typ) ->
          let _0_392 = translate_type env typ  in
          { name; typ = _0_392; mut = false }

and translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2578) ->
          EBound (find env name)
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          EOp
            (let _0_394 = FStar_Util.must (mk_op op)  in
             let _0_393 = FStar_Util.must (mk_width m)  in (_0_394, _0_393))
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          EOp
            (let _0_395 = FStar_Util.must (mk_bool_op op)  in (_0_395, Bool))
      | FStar_Extraction_ML_Syntax.MLE_Name n -> EQualified n
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____2588);
                           FStar_Extraction_ML_Syntax.mllb_tysc = Some
                             ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___121_2604  ->
                 match uu___121_2604 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____2605 -> false) flags
             in
          let uu____2606 =
            if is_mut
            then
              let _0_399 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let _0_396 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    _0_396 = "FStar.ST.stackref" -> t
                | uu____2614 ->
                    failwith
                      (let _0_397 =
                         FStar_Extraction_ML_Code.string_of_mlty ([], "") typ
                          in
                       FStar_Util.format1
                         "unexpected: bad desugaring of Mutable (typ is %s)"
                         _0_397)
                 in
              let _0_398 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____2616,body::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____2618;
                    FStar_Extraction_ML_Syntax.loc = uu____2619;_} -> body
                | uu____2621 ->
                    failwith "unexpected: bad desugaring of Mutable"
                 in
              (_0_399, _0_398)
            else (typ, body)  in
          (match uu____2606 with
           | (typ,body) ->
               let binder =
                 let _0_400 = translate_type env typ  in
                 { name; typ = _0_400; mut = is_mut }  in
               let body = translate_expr env body  in
               let env = extend env name is_mut  in
               let continuation = translate_expr env continuation  in
               ELet (binder, body, continuation))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          EMatch
            (let _0_402 = translate_expr env expr  in
             let _0_401 = translate_branches env branches  in
             (_0_402, _0_401))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2645;
             FStar_Extraction_ML_Syntax.loc = uu____2646;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v,uu____2648);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2649;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2650;_}::[])
          when
          (let _0_403 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           _0_403 = "FStar.ST.op_Bang") && (is_mutable env v)
          -> EBound (find env v)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2653;
             FStar_Extraction_ML_Syntax.loc = uu____2654;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v,uu____2656);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2657;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2658;_}::e::[])
          when
          (let _0_404 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           _0_404 = "FStar.ST.op_Colon_Equals") && (is_mutable env v)
          ->
          EAssign
            (let _0_406 = EBound (find env v)  in
             let _0_405 = translate_expr env e  in (_0_406, _0_405))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2662;
             FStar_Extraction_ML_Syntax.loc = uu____2663;_},e1::e2::[])
          when
          (let _0_407 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           _0_407 = "FStar.Buffer.index") ||
            (let _0_408 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
             _0_408 = "FStar.Buffer.op_Array_Access")
          ->
          EBufRead
            (let _0_410 = translate_expr env e1  in
             let _0_409 = translate_expr env e2  in (_0_410, _0_409))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2668;
             FStar_Extraction_ML_Syntax.loc = uu____2669;_},e1::e2::[])
          when
          let _0_411 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_411 = "FStar.Buffer.create" ->
          EBufCreate
            (let _0_413 = translate_expr env e1  in
             let _0_412 = translate_expr env e2  in (Stack, _0_413, _0_412))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2674;
             FStar_Extraction_ML_Syntax.loc = uu____2675;_},_e0::e1::e2::[])
          when
          let _0_414 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_414 = "FStar.Buffer.rcreate" ->
          EBufCreate
            (let _0_416 = translate_expr env e1  in
             let _0_415 = translate_expr env e2  in (Eternal, _0_416, _0_415))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2681;
             FStar_Extraction_ML_Syntax.loc = uu____2682;_},e2::[])
          when
          let _0_417 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_417 = "FStar.Buffer.createL" ->
          let rec list_elements acc e2 =
            match e2.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd::tl::[]) ->
                list_elements (hd :: acc) tl
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____2708 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!"
             in
          let list_elements = list_elements []  in
          EBufCreateL
            (let _0_419 =
               let _0_418 = list_elements e2  in
               FStar_List.map (translate_expr env) _0_418  in
             (Stack, _0_419))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2716;
             FStar_Extraction_ML_Syntax.loc = uu____2717;_},e1::e2::_e3::[])
          when
          let _0_420 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_420 = "FStar.Buffer.sub" ->
          EBufSub
            (let _0_422 = translate_expr env e1  in
             let _0_421 = translate_expr env e2  in (_0_422, _0_421))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2723;
             FStar_Extraction_ML_Syntax.loc = uu____2724;_},e1::e2::[])
          when
          let _0_423 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_423 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2729;
             FStar_Extraction_ML_Syntax.loc = uu____2730;_},e1::e2::[])
          when
          let _0_424 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_424 = "FStar.Buffer.offset" ->
          EBufSub
            (let _0_426 = translate_expr env e1  in
             let _0_425 = translate_expr env e2  in (_0_426, _0_425))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2735;
             FStar_Extraction_ML_Syntax.loc = uu____2736;_},e1::e2::e3::[])
          when
          (let _0_427 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           _0_427 = "FStar.Buffer.upd") ||
            (let _0_428 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
             _0_428 = "FStar.Buffer.op_Array_Assignment")
          ->
          EBufWrite
            (let _0_431 = translate_expr env e1  in
             let _0_430 = translate_expr env e2  in
             let _0_429 = translate_expr env e3  in (_0_431, _0_430, _0_429))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2742;
             FStar_Extraction_ML_Syntax.loc = uu____2743;_},uu____2744::[])
          when
          let _0_432 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_432 = "FStar.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2747;
             FStar_Extraction_ML_Syntax.loc = uu____2748;_},uu____2749::[])
          when
          let _0_433 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_433 = "FStar.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2752;
             FStar_Extraction_ML_Syntax.loc = uu____2753;_},e1::e2::e3::e4::e5::[])
          when
          let _0_434 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_434 = "FStar.Buffer.blit" ->
          EBufBlit
            (let _0_439 = translate_expr env e1  in
             let _0_438 = translate_expr env e2  in
             let _0_437 = translate_expr env e3  in
             let _0_436 = translate_expr env e4  in
             let _0_435 = translate_expr env e5  in
             (_0_439, _0_438, _0_437, _0_436, _0_435))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2761;
             FStar_Extraction_ML_Syntax.loc = uu____2762;_},e1::e2::e3::[])
          when
          let _0_440 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_440 = "FStar.Buffer.fill" ->
          EBufFill
            (let _0_443 = translate_expr env e1  in
             let _0_442 = translate_expr env e2  in
             let _0_441 = translate_expr env e3  in (_0_443, _0_442, _0_441))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2768;
             FStar_Extraction_ML_Syntax.loc = uu____2769;_},uu____2770::[])
          when
          let _0_444 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_444 = "FStar.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2773;
             FStar_Extraction_ML_Syntax.loc = uu____2774;_},e::[])
          when
          let _0_445 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_445 = "Obj.repr" ->
          ECast (let _0_446 = translate_expr env e  in (_0_446, TAny))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____2779;
             FStar_Extraction_ML_Syntax.loc = uu____2780;_},args)
          when (is_machine_int m) && (is_op op) ->
          let _0_448 = FStar_Util.must (mk_width m)  in
          let _0_447 = FStar_Util.must (mk_op op)  in
          mk_op_app env _0_448 _0_447 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____2786;
             FStar_Extraction_ML_Syntax.loc = uu____2787;_},args)
          when is_bool_op op ->
          let _0_449 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool _0_449 args
      | FStar_Extraction_ML_Syntax.MLE_App
        ({
           FStar_Extraction_ML_Syntax.expr =
             FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],"int_to_t");
           FStar_Extraction_ML_Syntax.mlty = _;
           FStar_Extraction_ML_Syntax.loc = _;_},{
                                                   FStar_Extraction_ML_Syntax.expr
                                                     =
                                                     FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_Int
                                                     (c,None ));
                                                   FStar_Extraction_ML_Syntax.mlty
                                                     = _;
                                                   FStar_Extraction_ML_Syntax.loc
                                                     = _;_}::[])
        |FStar_Extraction_ML_Syntax.MLE_App
        ({
           FStar_Extraction_ML_Syntax.expr =
             FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],"uint_to_t");
           FStar_Extraction_ML_Syntax.mlty = _;
           FStar_Extraction_ML_Syntax.loc = _;_},{
                                                   FStar_Extraction_ML_Syntax.expr
                                                     =
                                                     FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_Int
                                                     (c,None ));
                                                   FStar_Extraction_ML_Syntax.mlty
                                                     = _;
                                                   FStar_Extraction_ML_Syntax.loc
                                                     = _;_}::[])
          when is_machine_int m ->
          EConstant
            (let _0_450 = FStar_Util.must (mk_width m)  in (_0_450, c))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____2816;
             FStar_Extraction_ML_Syntax.loc = uu____2817;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2819;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2820;_}::[])
          ->
          (match e with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____2824 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____2826;
             FStar_Extraction_ML_Syntax.loc = uu____2827;_},arg::[])
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
            ECast
              (let _0_451 = translate_expr env arg  in
               (_0_451, (TInt UInt64)))
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              ECast
                ((let _0_452 = translate_expr env arg  in
                  (_0_452, (TInt UInt32))))
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                ECast
                  ((let _0_453 = translate_expr env arg  in
                    (_0_453, (TInt UInt16))))
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  ECast
                    ((let _0_454 = translate_expr env arg  in
                      (_0_454, (TInt UInt8))))
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    ECast
                      ((let _0_455 = translate_expr env arg  in
                        (_0_455, (TInt Int64))))
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      ECast
                        ((let _0_456 = translate_expr env arg  in
                          (_0_456, (TInt Int32))))
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        ECast
                          ((let _0_457 = translate_expr env arg  in
                            (_0_457, (TInt Int16))))
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          ECast
                            ((let _0_458 = translate_expr env arg  in
                              (_0_458, (TInt Int8))))
                        else
                          EApp
                            ((let _0_460 =
                                let _0_459 = translate_expr env arg  in
                                [_0_459]  in
                              ((EQualified (["FStar"; "Int"; "Cast"], c)),
                                _0_460)))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____2844;
             FStar_Extraction_ML_Syntax.loc = uu____2845;_},args)
          ->
          EApp
            (let _0_461 = FStar_List.map (translate_expr env) args  in
             ((EQualified (path, function_name)), _0_461))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2854);
             FStar_Extraction_ML_Syntax.mlty = uu____2855;
             FStar_Extraction_ML_Syntax.loc = uu____2856;_},args)
          ->
          EApp
            (let _0_463 = EBound (find env name)  in
             let _0_462 = FStar_List.map (translate_expr env) args  in
             (_0_463, _0_462))
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e,t_from,t_to) ->
          ECast
            (let _0_465 = translate_expr env e  in
             let _0_464 = translate_type env t_to  in (_0_465, _0_464))
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____2864,fields) ->
          EFlat
            (let _0_468 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
                in
             let _0_467 =
               FStar_List.map
                 (fun uu____2881  ->
                    match uu____2881 with
                    | (field,expr) ->
                        let _0_466 = translate_expr env expr  in
                        (field, _0_466)) fields
                in
             (_0_468, _0_467))
      | FStar_Extraction_ML_Syntax.MLE_Proj (e,path) ->
          EField
            (let _0_470 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
                in
             let _0_469 = translate_expr env e  in
             (_0_470, _0_469, (Prims.snd path)))
      | FStar_Extraction_ML_Syntax.MLE_Let uu____2891 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head,uu____2899) ->
          failwith
            (let _0_471 =
               FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head  in
             FStar_Util.format1
               "todo: translate_expr [MLE_App] (head is: %s)" _0_471)
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          ESequence (FStar_List.map (translate_expr env) seqs)
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          ETuple (FStar_List.map (translate_expr env) es)
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____2907,cons),es) ->
          ECons
            (let _0_473 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
                in
             let _0_472 = FStar_List.map (translate_expr env) es  in
             (_0_473, cons, _0_472))
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env = add_binders env args  in
          EFun (let _0_474 = translate_expr env body  in (binders, _0_474))
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          EIfThenElse
            (let _0_477 = translate_expr env e1  in
             let _0_476 = translate_expr env e2  in
             let _0_475 =
               match e3 with
               | None  -> EUnit
               | Some e3 -> translate_expr env e3  in
             (_0_477, _0_476, _0_475))
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____2936 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____2940 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____2948 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            TApp
              (let _0_478 = FStar_List.map (translate_type env) ts  in
               (lid, _0_478))
          else TQualified lid
      | uu____2963 -> failwith "invalid argument: assert_lid"

and translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      Prims.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list ->
      (pattern * expr) Prims.list
  =
  fun env  -> fun branches  -> FStar_List.map (translate_branch env) branches

and translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      Prims.option * FStar_Extraction_ML_Syntax.mlexpr) -> (pattern * expr)
  =
  fun env  ->
    fun uu____2978  ->
      match uu____2978 with
      | (pat,guard,expr) ->
          if guard = None
          then
            let uu____2993 = translate_pat env pat  in
            (match uu____2993 with
             | (env,pat) ->
                 let _0_479 = translate_expr env expr  in (pat, _0_479))
          else failwith "todo: translate_branch"

and translate_pat :
  env -> FStar_Extraction_ML_Syntax.mlpattern -> (env * pattern) =
  fun env  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____3009) ->
          let env = extend env name false  in
          (env, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env = extend env "_" false  in
          (env, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3012,cons),ps) ->
          let uu____3022 =
            FStar_List.fold_left
              (fun uu____3029  ->
                 fun p  ->
                   match uu____3029 with
                   | (env,acc) ->
                       let uu____3041 = translate_pat env p  in
                       (match uu____3041 with | (env,p) -> (env, (p :: acc))))
              (env, []) ps
             in
          (match uu____3022 with
           | (env,ps) -> (env, (PCons (cons, (FStar_List.rev ps)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____3058,ps) ->
          let uu____3068 =
            FStar_List.fold_left
              (fun uu____3081  ->
                 fun uu____3082  ->
                   match (uu____3081, uu____3082) with
                   | ((env,acc),(field,p)) ->
                       let uu____3119 = translate_pat env p  in
                       (match uu____3119 with
                        | (env,p) -> (env, ((field, p) :: acc)))) (env, [])
              ps
             in
          (match uu____3068 with
           | (env,ps) -> (env, (PRecord (FStar_List.rev ps))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____3153 =
            FStar_List.fold_left
              (fun uu____3160  ->
                 fun p  ->
                   match uu____3160 with
                   | (env,acc) ->
                       let uu____3172 = translate_pat env p  in
                       (match uu____3172 with | (env,p) -> (env, (p :: acc))))
              (env, []) ps
             in
          (match uu____3153 with
           | (env,ps) -> (env, (PTuple (FStar_List.rev ps))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____3188 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____3191 ->
          failwith "todo: translate_pat [MLP_Branch]"

and translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some uu____3198) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____3206 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3207 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____3208 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3209 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (uu____3211,None ) ->
        failwith "todo: translate_expr [MLC_Int]"

and mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          EApp
            (let _0_480 = FStar_List.map (translate_expr env) args  in
             ((EOp (op, w)), _0_480))
