open Prims
type decl =
  | DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) *
  typ * expr) 
  | DFunction of (cc Prims.option * flag Prims.list * typ * (Prims.string
  Prims.list * Prims.string) * binder Prims.list * expr) 
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
    match projectee with | DGlobal _0 -> true | uu____293 -> false
  
let __proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * typ * expr)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let uu___is_DFunction : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____341 -> false
  
let __proj__DFunction__item___0 :
  decl ->
    (cc Prims.option * flag Prims.list * typ * (Prims.string Prims.list *
      Prims.string) * binder Prims.list * expr)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let uu___is_DTypeAlias : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____395 -> false
  
let __proj__DTypeAlias__item___0 :
  decl -> ((Prims.string Prims.list * Prims.string) * Prims.int * typ) =
  fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let uu___is_DTypeFlat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____436 -> false
  
let __proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string *
      (typ * Prims.bool)) Prims.list)
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let uu___is_DExternal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____488 -> false
  
let __proj__DExternal__item___0 :
  decl -> (cc Prims.option * (Prims.string Prims.list * Prims.string) * typ)
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let uu___is_DTypeVariant : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____535 -> false
  
let __proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string *
      (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list)
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let uu___is_StdCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____588 -> false
  
let uu___is_CDecl : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____592 -> false
  
let uu___is_FastCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____596 -> false
  
let uu___is_Private : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____600 -> false
  
let uu___is_NoExtract : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____604 -> false
  
let uu___is_CInline : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____608 -> false
  
let uu___is_Substitute : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____612 -> false
  
let uu___is_Eternal : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____616 -> false
  
let uu___is_Stack : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____620 -> false
  
let uu___is_EBound : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____625 -> false
  
let __proj__EBound__item___0 : expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let uu___is_EQualified : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____640 -> false
  
let __proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let uu___is_EConstant : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____663 -> false
  
let __proj__EConstant__item___0 : expr -> (width * Prims.string) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let uu___is_EUnit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____680 -> false
  
let uu___is_EApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____688 -> false
  
let __proj__EApp__item___0 : expr -> (expr * expr Prims.list) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let uu___is_ELet : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____712 -> false
  
let __proj__ELet__item___0 : expr -> (binder * expr * expr) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let uu___is_EIfThenElse : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____736 -> false
  
let __proj__EIfThenElse__item___0 : expr -> (expr * expr * expr) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let uu___is_ESequence : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____758 -> false
  
let __proj__ESequence__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let uu___is_EAssign : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____775 -> false
  
let __proj__EAssign__item___0 : expr -> (expr * expr) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let uu___is_EBufCreate : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____796 -> false
  
let __proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let uu___is_EBufRead : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____819 -> false
  
let __proj__EBufRead__item___0 : expr -> (expr * expr) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let uu___is_EBufWrite : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____840 -> false
  
let __proj__EBufWrite__item___0 : expr -> (expr * expr * expr) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let uu___is_EBufSub : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____863 -> false
  
let __proj__EBufSub__item___0 : expr -> (expr * expr) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let uu___is_EBufBlit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____886 -> false
  
let __proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let uu___is_EMatch : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____918 -> false
  
let __proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list) =
  fun projectee  -> match projectee with | EMatch _0 -> _0 
let uu___is_EOp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____947 -> false
  
let __proj__EOp__item___0 : expr -> (op * width) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let uu___is_ECast : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____967 -> false
  
let __proj__ECast__item___0 : expr -> (expr * typ) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let uu___is_EPushFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____984 -> false
  
let uu___is_EPopFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____988 -> false
  
let uu___is_EBool : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____993 -> false
  
let __proj__EBool__item___0 : expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let uu___is_EAny : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1004 -> false
  
let uu___is_EAbort : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1008 -> false
  
let uu___is_EReturn : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1013 -> false
  
let __proj__EReturn__item___0 : expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let uu___is_EFlat : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1030 -> false
  
let __proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let uu___is_EField : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1060 -> false
  
let __proj__EField__item___0 : expr -> (typ * expr * Prims.string) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let uu___is_EWhile : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1083 -> false
  
let __proj__EWhile__item___0 : expr -> (expr * expr) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let uu___is_EBufCreateL : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1104 -> false
  
let __proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let uu___is_ETuple : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1126 -> false
  
let __proj__ETuple__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let uu___is_ECons : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1145 -> false
  
let __proj__ECons__item___0 : expr -> (typ * Prims.string * expr Prims.list)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let uu___is_EBufFill : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____1172 -> false
  
let __proj__EBufFill__item___0 : expr -> (expr * expr * expr) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let uu___is_EString : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____1193 -> false
  
let __proj__EString__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____1204 -> false 
let uu___is_AddW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____1208 -> false
  
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____1212 -> false 
let uu___is_SubW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____1216 -> false
  
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____1220 -> false 
let uu___is_DivW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____1224 -> false
  
let uu___is_Mult : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____1228 -> false
  
let uu___is_MultW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____1232 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____1236 -> false 
let uu___is_BOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____1240 -> false 
let uu___is_BAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____1244 -> false
  
let uu___is_BXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____1248 -> false
  
let uu___is_BShiftL : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____1252 -> false
  
let uu___is_BShiftR : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____1256 -> false
  
let uu___is_BNot : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____1260 -> false
  
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____1264 -> false 
let uu___is_Neq : op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____1268 -> false 
let uu___is_Lt : op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____1272 -> false 
let uu___is_Lte : op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____1276 -> false 
let uu___is_Gt : op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____1280 -> false 
let uu___is_Gte : op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____1284 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____1288 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____1292 -> false 
let uu___is_Xor : op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____1296 -> false 
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____1300 -> false 
let uu___is_PUnit : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____1304 -> false
  
let uu___is_PBool : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____1309 -> false
  
let __proj__PBool__item___0 : pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let uu___is_PVar : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____1321 -> false
  
let __proj__PVar__item___0 : pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let uu___is_PCons : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____1336 -> false
  
let __proj__PCons__item___0 : pattern -> (Prims.string * pattern Prims.list)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let uu___is_PTuple : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____1358 -> false
  
let __proj__PTuple__item___0 : pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let uu___is_PRecord : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____1376 -> false
  
let __proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let uu___is_UInt8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____1396 -> false
  
let uu___is_UInt16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____1400 -> false
  
let uu___is_UInt32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____1404 -> false
  
let uu___is_UInt64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____1408 -> false
  
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____1412 -> false
  
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____1416 -> false
  
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____1420 -> false
  
let uu___is_Int64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____1424 -> false
  
let uu___is_Bool : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____1428 -> false
  
let uu___is_Int : width -> Prims.bool =
  fun projectee  -> match projectee with | Int  -> true | uu____1432 -> false 
let uu___is_UInt : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt  -> true | uu____1436 -> false
  
let uu___is_TInt : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____1453 -> false
  
let __proj__TInt__item___0 : typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let uu___is_TBuf : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____1465 -> false
  
let __proj__TBuf__item___0 : typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let uu___is_TUnit : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____1476 -> false
  
let uu___is_TQualified : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____1484 -> false
  
let __proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let uu___is_TBool : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____1504 -> false
  
let uu___is_TAny : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____1508 -> false
  
let uu___is_TArrow : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____1515 -> false
  
let __proj__TArrow__item___0 : typ -> (typ * typ) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let uu___is_TZ : typ -> Prims.bool =
  fun projectee  -> match projectee with | TZ  -> true | uu____1532 -> false 
let uu___is_TBound : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____1537 -> false
  
let __proj__TBound__item___0 : typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let uu___is_TApp : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____1555 -> false
  
let __proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let uu___is_TTuple : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____1586 -> false
  
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
let current_version : Prims.int = (Prims.parse_int "19") 
type file = (Prims.string * program)
type binary_format = (version * file Prims.list)
let fst3 uu____1639 = match uu____1639 with | (x,uu____1644,uu____1645) -> x 
let snd3 uu____1659 = match uu____1659 with | (uu____1663,x,uu____1665) -> x 
let thd3 uu____1679 = match uu____1679 with | (uu____1683,uu____1684,x) -> x 
let mk_width : Prims.string -> width Prims.option =
  fun uu___139_1689  ->
    match uu___139_1689 with
    | "UInt8" -> Some UInt8
    | "UInt16" -> Some UInt16
    | "UInt32" -> Some UInt32
    | "UInt64" -> Some UInt64
    | "Int8" -> Some Int8
    | "Int16" -> Some Int16
    | "Int32" -> Some Int32
    | "Int64" -> Some Int64
    | uu____1691 -> None
  
let mk_bool_op : Prims.string -> op Prims.option =
  fun uu___140_1695  ->
    match uu___140_1695 with
    | "op_Negation" -> Some Not
    | "op_AmpAmp" -> Some And
    | "op_BarBar" -> Some Or
    | "op_Equality" -> Some Eq
    | "op_disEquality" -> Some Neq
    | uu____1697 -> None
  
let is_bool_op : Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> None 
let mk_op : Prims.string -> op Prims.option =
  fun uu___141_1705  ->
    match uu___141_1705 with
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
    | uu____1707 -> None
  
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
        let uu___146_1774 = env  in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___124_1809.names_t);
          module_name = (uu___124_1809.module_name)
        }
  
let extend_t : env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___147_1781 = env  in
      {
        names = (uu___125_1816.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___125_1816.module_name)
      }
  
let find_name : env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____1788 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____1788 with
      | Some name -> name
      | None  -> failwith "internal error: name not found"
  
let is_mutable : env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> (find_name env x).mut 
let find : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____1807 ->
          failwith
            (FStar_Util.format1 "Internal error: name not found %s\n" x)
  
let find_t : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____1817 ->
          failwith
            (FStar_Util.format1 "Internal error: name not found %s\n" x)
  
let add_binders env binders =
  FStar_List.fold_left
    (fun env1  ->
       fun uu____1885  ->
         match uu____1885 with
         | ((name,uu____1891),uu____1892) -> extend env1 name false) env
    binders
  
let rec translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____1945  ->
    match uu____1945 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____1976 = m  in
               match uu____1976 with
               | ((prefix,final),uu____1988,uu____1989) ->
                   FStar_String.concat "." (FStar_List.append prefix [final])
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____2043 = translate_module m in Some uu____2043)
             with
             | e ->
                 ((let _0_560 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     _0_560);
                  None)) modules

and translate_module :
  ((Prims.string Prims.list * Prims.string) *
    (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule)
    Prims.option * FStar_Extraction_ML_Syntax.mllib) -> file
  =
  fun uu____2009  ->
    match uu____2009 with
    | (module_name,modul,uu____2021) ->
        let module_name =
          FStar_List.append (Prims.fst module_name) [Prims.snd module_name]
           in
        let program =
          match modul with
          | Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____2045 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name), program)

and translate_flags :
  FStar_Extraction_ML_Syntax.c_flag Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___120_2093  ->
         match uu___120_2093 with
         | FStar_Extraction_ML_Syntax.Private  -> Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  -> Some NoExtract
         | FStar_Extraction_ML_Syntax.Attribute "c_inline" -> Some CInline
         | FStar_Extraction_ML_Syntax.Attribute "substitute" ->
             Some Substitute
         | FStar_Extraction_ML_Syntax.Attribute a ->
             (FStar_Util.print1_warning "Warning: unrecognized attribute %s"
                a;
              None)
         | uu____2057 -> None) flags

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
              (fun uu___121_2142  ->
                 match uu___121_2142 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2106 -> false) flags
             in
          let env =
            match flavor = FStar_Extraction_ML_Syntax.Rec with
            | true  -> extend env name false
            | uu____2108 -> env  in
          let rec find_return_type uu___144_2112 =
            match uu___144_2112 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2113,uu____2114,t)
                -> find_return_type t
            | t -> t  in
          let t =
            let _0_561 = find_return_type t0  in translate_type env _0_561
             in
          let binders = translate_binders env args  in
          let env = add_binders env args  in
          let name = ((env.module_name), name)  in
          let flags = translate_flags flags  in
          (match assumed with
           | true  ->
               Some
                 (DExternal
                    (let _0_562 = translate_type env t0  in
                     (None, name, _0_562)))
           | uu____2133 ->
               (try
                  let body = translate_expr env body  in
                  Some (DFunction (None, flags, t, name, binders, body))
                with
                | e ->
                    ((let _0_563 = FStar_Util.print_exn e  in
                      FStar_Util.print2
                        "Warning: writing a stub for %s (%s)\n"
                        (Prims.snd name) _0_563);
                     Some (DFunction (None, flags, t, name, binders, EAbort)))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2224);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2226;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2228;_}::[])
          ->
          let flags = translate_flags flags  in
          let t = translate_type env t  in
          let name = ((env.module_name), name)  in
          (try
             let expr = translate_expr env expr  in
             Some (DGlobal (flags, name, t, expr))
           with
           | e ->
               ((let _0_564 = FStar_Util.print_exn e  in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (Prims.snd name1) uu____2254);
                Some (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____2260,uu____2261,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____2263);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____2265;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____2266;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____2267;_}::uu____2268)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | Some (idents,t) ->
                let _0_567 =
                  let _0_565 = FStar_List.map Prims.fst idents  in
                  FStar_String.concat ", " _0_565  in
                let _0_566 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n" _0_567
                  _0_566
            | None  -> ());
           None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____2285 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____2287 -> None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2248  ->
                   match uu____2248 with
                   | (name,uu____2252) -> extend_t env name) env args
             in
          (match assumed with
           | true  -> None
           | uu____2254 ->
               Some
                 (DTypeAlias
                    (let _0_568 = translate_type env t  in
                     (name, (FStar_List.length args), _0_568))))
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2340,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2294  ->
                   match uu____2294 with
                   | (name,uu____2298) -> extend_t env name) env args
             in
          Some
            (DTypeFlat
               (let _0_571 =
                  FStar_List.map
                    (fun uu____2315  ->
                       match uu____2315 with
                       | (f,t) ->
                           let _0_570 =
                             let _0_569 = translate_type env t  in
                             (_0_569, false)  in
                           (f, _0_570)) fields
                   in
                (name, (FStar_List.length args), _0_571)))
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2429,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2361  ->
                   match uu____2361 with
                   | (name,uu____2365) -> extend_t env name) env args
             in
          Some
            (DTypeVariant
               (let _0_578 =
                  FStar_List.mapi
                    (fun i  ->
                       fun uu____2390  ->
                         match uu____2390 with
                         | (cons,ts) ->
                             let _0_577 =
                               FStar_List.mapi
                                 (fun j  ->
                                    fun t  ->
                                      let _0_576 =
                                        let _0_573 =
                                          FStar_Util.string_of_int i  in
                                        let _0_572 =
                                          FStar_Util.string_of_int j  in
                                        FStar_Util.format2 "x%s%s" _0_573
                                          _0_572
                                         in
                                      let _0_575 =
                                        let _0_574 = translate_type env t  in
                                        (_0_574, false)  in
                                      (_0_576, _0_575)) ts
                                in
                             (cons, _0_577)) branches
                   in
                (name, (FStar_List.length args), _0_578)))
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2559,name,_mangled_name,uu____2562,uu____2563)::uu____2564)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2586 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2588 ->
          failwith "todo: translate_decl [MLM_Exn]"

and translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple []
        |FStar_Extraction_ML_Syntax.MLTY_Top  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____2455) ->
          TBound (find_t env name)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2457,t2) ->
          TArrow
            (let _0_580 = translate_type env t1  in
             let _0_579 = translate_type env t2  in (_0_580, _0_579))
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let _0_581 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_581 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let _0_582 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_582 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____2618 = FStar_Util.must (mk_width m) in TInt uu____2618
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____2625 = FStar_Util.must (mk_width m) in TInt uu____2625
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let _0_583 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_583 = "FStar.Buffer.buffer" -> TBuf (translate_type env arg)
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2478::[],p) when
          let _0_584 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_584 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,("Prims"::[],t1)) when
          FStar_Util.starts_with t1 "tuple" ->
          let uu____2652 = FStar_List.map (translate_type env) args in
          TTuple uu____2652
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          (match (FStar_List.length args) > (Prims.parse_int "0") with
           | true  ->
               TApp
                 (let _0_585 = FStar_List.map (translate_type env) args  in
                  (lid, _0_585))
           | uu____2506 -> TQualified lid)
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
    fun uu____2517  ->
      match uu____2517 with
      | ((name,uu____2521),typ) ->
          let _0_586 = translate_type env typ  in
          { name; typ = _0_586; mut = false }

and translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2697) ->
          let uu____2698 = find env name in EBound uu____2698
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          EOp
            (let _0_588 = FStar_Util.must (mk_op op)  in
             let _0_587 = FStar_Util.must (mk_width m)  in (_0_588, _0_587))
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          EOp
            (let _0_589 = FStar_Util.must (mk_bool_op op)  in (_0_589, Bool))
      | FStar_Extraction_ML_Syntax.MLE_Name n -> EQualified n
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____2717);
                           FStar_Extraction_ML_Syntax.mllb_tysc = Some
                             ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___123_2733  ->
                 match uu___123_2733 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____2556 -> false) flags
             in
          let uu____2557 =
            match is_mut with
            | true  ->
                let _0_593 =
                  match typ with
                  | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                      let _0_590 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      _0_590 = "FStar.ST.stackref" -> t
                  | uu____2565 ->
                      failwith
                        (let _0_591 =
                           FStar_Extraction_ML_Code.string_of_mlty ([], "")
                             typ
                            in
                         FStar_Util.format1
                           "unexpected: bad desugaring of Mutable (typ is %s)"
                           _0_591)
                   in
                let _0_592 =
                  match body with
                  | {
                      FStar_Extraction_ML_Syntax.expr =
                        FStar_Extraction_ML_Syntax.MLE_App
                        (uu____2567,body::[]);
                      FStar_Extraction_ML_Syntax.mlty = uu____2569;
                      FStar_Extraction_ML_Syntax.loc = uu____2570;_} -> body
                  | uu____2572 ->
                      failwith "unexpected: bad desugaring of Mutable"
                   in
                (_0_593, _0_592)
            | uu____2573 -> (typ, body)  in
          (match uu____2557 with
           | (typ,body) ->
               let binder =
                 let _0_594 = translate_type env typ  in
                 { name; typ = _0_594; mut = is_mut }  in
               let body = translate_expr env body  in
               let env = extend env name is_mut  in
               let continuation = translate_expr env continuation  in
               ELet (binder, body, continuation))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          EMatch
            (let _0_596 = translate_expr env expr  in
             let _0_595 = translate_branches env branches  in
             (_0_596, _0_595))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2791;
             FStar_Extraction_ML_Syntax.loc = uu____2792;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____2794);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2795;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2796;_}::[])
          when
          (let _0_597 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           _0_597 = "FStar.ST.op_Bang") && (is_mutable env v)
          -> EBound (find env v)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2801;
             FStar_Extraction_ML_Syntax.loc = uu____2802;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____2804);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2805;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2806;_}::e1::[])
          when
          (let _0_598 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           _0_598 = "FStar.ST.op_Colon_Equals") && (is_mutable env v)
          ->
          EAssign
            (let _0_600 = EBound (find env v)  in
             let _0_599 = translate_expr env e  in (_0_600, _0_599))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2817;
             FStar_Extraction_ML_Syntax.loc = uu____2818;_},e1::e2::[])
          when
          (let _0_601 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           _0_601 = "FStar.Buffer.index") ||
            (let _0_602 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
             _0_602 = "FStar.Buffer.op_Array_Access")
          ->
          EBufRead
            (let _0_604 = translate_expr env e1  in
             let _0_603 = translate_expr env e2  in (_0_604, _0_603))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2830;
             FStar_Extraction_ML_Syntax.loc = uu____2831;_},e1::e2::[])
          when
          let _0_605 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_605 = "FStar.Buffer.create" ->
          EBufCreate
            (let _0_607 = translate_expr env e1  in
             let _0_606 = translate_expr env e2  in (Stack, _0_607, _0_606))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2843;
             FStar_Extraction_ML_Syntax.loc = uu____2844;_},_e0::e1::e2::[])
          when
          let _0_608 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_608 = "FStar.Buffer.rcreate" ->
          EBufCreate
            (let _0_610 = translate_expr env e1  in
             let _0_609 = translate_expr env e2  in (Eternal, _0_610, _0_609))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2857;
             FStar_Extraction_ML_Syntax.loc = uu____2858;_},e2::[])
          when
          let _0_611 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_611 = "FStar.Buffer.createL" ->
          let rec list_elements acc e2 =
            match e2.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____2885 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!"
             in
          let list_elements = list_elements []  in
          EBufCreateL
            (let _0_613 =
               let _0_612 = list_elements e2  in
               FStar_List.map (translate_expr env) _0_612  in
             (Stack, _0_613))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2901;
             FStar_Extraction_ML_Syntax.loc = uu____2902;_},e1::e2::_e3::[])
          when
          let _0_614 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_614 = "FStar.Buffer.sub" ->
          EBufSub
            (let _0_616 = translate_expr env e1  in
             let _0_615 = translate_expr env e2  in (_0_616, _0_615))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2914;
             FStar_Extraction_ML_Syntax.loc = uu____2915;_},e1::e2::[])
          when
          let _0_617 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_617 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2921;
             FStar_Extraction_ML_Syntax.loc = uu____2922;_},e1::e2::[])
          when
          let _0_618 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_618 = "FStar.Buffer.offset" ->
          EBufSub
            (let _0_620 = translate_expr env e1  in
             let _0_619 = translate_expr env e2  in (_0_620, _0_619))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2933;
             FStar_Extraction_ML_Syntax.loc = uu____2934;_},e1::e2::e3::[])
          when
          (let _0_621 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           _0_621 = "FStar.Buffer.upd") ||
            (let _0_622 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
             _0_622 = "FStar.Buffer.op_Array_Assignment")
          ->
          EBufWrite
            (let _0_625 = translate_expr env e1  in
             let _0_624 = translate_expr env e2  in
             let _0_623 = translate_expr env e3  in (_0_625, _0_624, _0_623))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2949;
             FStar_Extraction_ML_Syntax.loc = uu____2950;_},uu____2951::[])
          when
          let _0_626 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_626 = "FStar.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2955;
             FStar_Extraction_ML_Syntax.loc = uu____2956;_},uu____2957::[])
          when
          let _0_627 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_627 = "FStar.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2961;
             FStar_Extraction_ML_Syntax.loc = uu____2962;_},e1::e2::e3::e4::e5::[])
          when
          let _0_628 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_628 = "FStar.Buffer.blit" ->
          EBufBlit
            (let _0_633 = translate_expr env e1  in
             let _0_632 = translate_expr env e2  in
             let _0_631 = translate_expr env e3  in
             let _0_630 = translate_expr env e4  in
             let _0_629 = translate_expr env e5  in
             (_0_633, _0_632, _0_631, _0_630, _0_629))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2982;
             FStar_Extraction_ML_Syntax.loc = uu____2983;_},e1::e2::e3::[])
          when
          let _0_634 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_634 = "FStar.Buffer.fill" ->
          EBufFill
            (let _0_637 = translate_expr env e1  in
             let _0_636 = translate_expr env e2  in
             let _0_635 = translate_expr env e3  in (_0_637, _0_636, _0_635))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2997;
             FStar_Extraction_ML_Syntax.loc = uu____2998;_},uu____2999::[])
          when
          let _0_638 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_638 = "FStar.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3003;
             FStar_Extraction_ML_Syntax.loc = uu____3004;_},e1::[])
          when
          let _0_639 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          _0_639 = "Obj.repr" ->
          ECast (let _0_640 = translate_expr env e  in (_0_640, TAny))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3014;
             FStar_Extraction_ML_Syntax.loc = uu____3015;_},args)
          when (is_machine_int m) && (is_op op) ->
          let _0_642 = FStar_Util.must (mk_width m)  in
          let _0_641 = FStar_Util.must (mk_op op)  in
          mk_op_app env _0_642 _0_641 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3023;
             FStar_Extraction_ML_Syntax.loc = uu____3024;_},args)
          when is_bool_op op ->
          let _0_643 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool _0_643 args
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
            (let _0_644 = FStar_Util.must (mk_width m)  in (_0_644, c))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____3058;
             FStar_Extraction_ML_Syntax.loc = uu____3059;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3061;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3062;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____3066 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____3068;
             FStar_Extraction_ML_Syntax.loc = uu____3069;_},arg::[])
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
          (match (FStar_Util.ends_with c "uint64") && is_known_type with
           | true  ->
               ECast
                 (let _0_645 = translate_expr env arg  in
                  (_0_645, (TInt UInt64)))
           | uu____2783 ->
               (match (FStar_Util.ends_with c "uint32") && is_known_type with
                | true  ->
                    ECast
                      (let _0_646 = translate_expr env arg  in
                       (_0_646, (TInt UInt32)))
                | uu____2784 ->
                    (match (FStar_Util.ends_with c "uint16") && is_known_type
                     with
                     | true  ->
                         ECast
                           (let _0_647 = translate_expr env arg  in
                            (_0_647, (TInt UInt16)))
                     | uu____2785 ->
                         (match (FStar_Util.ends_with c "uint8") &&
                                  is_known_type
                          with
                          | true  ->
                              ECast
                                (let _0_648 = translate_expr env arg  in
                                 (_0_648, (TInt UInt8)))
                          | uu____2786 ->
                              (match (FStar_Util.ends_with c "int64") &&
                                       is_known_type
                               with
                               | true  ->
                                   ECast
                                     (let _0_649 = translate_expr env arg  in
                                      (_0_649, (TInt Int64)))
                               | uu____2787 ->
                                   (match (FStar_Util.ends_with c "int32") &&
                                            is_known_type
                                    with
                                    | true  ->
                                        ECast
                                          (let _0_650 =
                                             translate_expr env arg  in
                                           (_0_650, (TInt Int32)))
                                    | uu____2788 ->
                                        (match (FStar_Util.ends_with c
                                                  "int16")
                                                 && is_known_type
                                         with
                                         | true  ->
                                             ECast
                                               (let _0_651 =
                                                  translate_expr env arg  in
                                                (_0_651, (TInt Int16)))
                                         | uu____2789 ->
                                             (match (FStar_Util.ends_with c
                                                       "int8")
                                                      && is_known_type
                                              with
                                              | true  ->
                                                  ECast
                                                    (let _0_652 =
                                                       translate_expr env arg
                                                        in
                                                     (_0_652, (TInt Int8)))
                                              | uu____2790 ->
                                                  EApp
                                                    (let _0_654 =
                                                       let _0_653 =
                                                         translate_expr env
                                                           arg
                                                          in
                                                       [_0_653]  in
                                                     ((EQualified
                                                         (["FStar";
                                                          "Int";
                                                          "Cast"], c)),
                                                       _0_654))))))))))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____3125;
             FStar_Extraction_ML_Syntax.loc = uu____3126;_},args)
          ->
          let uu____3132 =
            let uu____3136 = FStar_List.map (translate_expr env) args in
            ((EQualified (path, function_name)), uu____3136) in
          EApp uu____3132
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____3141);
             FStar_Extraction_ML_Syntax.mlty = uu____3142;
             FStar_Extraction_ML_Syntax.loc = uu____3143;_},args)
          ->
          EApp
            (let _0_655 = FStar_List.map (translate_expr env) args  in
             ((EQualified (path, function_name)), _0_655))
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e,t_from,t_to) ->
          ECast
            (let _0_657 = translate_expr env e  in
             let _0_656 = translate_type env t_to  in (_0_657, _0_656))
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____2807,fields) ->
          EFlat
            (let _0_660 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
                in
             let _0_659 =
               FStar_List.map
                 (fun uu____2824  ->
                    match uu____2824 with
                    | (field,expr) ->
                        let _0_658 = translate_expr env expr  in
                        (field, _0_658)) fields
                in
             (_0_660, _0_659))
      | FStar_Extraction_ML_Syntax.MLE_Proj (e,path) ->
          EField
            (let _0_662 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
                in
             let _0_661 = translate_expr env e  in
             (_0_662, _0_661, (Prims.snd path)))
      | FStar_Extraction_ML_Syntax.MLE_Let uu____2834 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head,uu____2842) ->
          failwith
            (let _0_663 =
               FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head  in
             FStar_Util.format1
               "todo: translate_expr [MLE_App] (head is: %s)" _0_663)
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____3225 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____3225
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          ETuple (FStar_List.map (translate_expr env) es)
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____2850,cons),es) ->
          ECons
            (let _0_665 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
                in
             let _0_664 = FStar_List.map (translate_expr env) es  in
             (_0_665, cons, _0_664))
      | FStar_Extraction_ML_Syntax.MLE_Fun uu____2861 ->
          failwith "todo: translate_expr [MLE_Fun]"
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          EIfThenElse
            (let _0_668 = translate_expr env e1  in
             let _0_667 = translate_expr env e2  in
             let _0_666 =
               match e3 with
               | None  -> EUnit
               | Some e3 -> translate_expr env e3  in
             (_0_668, _0_667, _0_666))
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____2873 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____3284 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____3292 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          (match (FStar_List.length ts) > (Prims.parse_int "0") with
           | true  ->
               TApp
                 (let _0_669 = FStar_List.map (translate_type env) ts  in
                  (lid, _0_669))
           | uu____2899 -> TQualified lid)
      | uu____2900 -> failwith "invalid argument: assert_lid"

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
    fun uu____3331  ->
      match uu____3331 with
      | (pat,guard,expr) ->
          (match guard = None with
           | true  ->
               let uu____2930 = translate_pat env pat  in
               (match uu____2930 with
                | (env,pat) ->
                    let _0_670 = translate_expr env expr  in (pat, _0_670))
           | uu____2937 -> failwith "todo: translate_branch")

and translate_pat :
  env -> FStar_Extraction_ML_Syntax.mlpattern -> (env * pattern) =
  fun env  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____2946) ->
          let env = extend env name false  in
          (env, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env = extend env "_" false  in
          (env, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____2949,cons),ps) ->
          let uu____2959 =
            FStar_List.fold_left
              (fun uu____2966  ->
                 fun p  ->
                   match uu____2966 with
                   | (env,acc) ->
                       let uu____2978 = translate_pat env p  in
                       (match uu____2978 with | (env,p) -> (env, (p :: acc))))
              (env, []) ps
             in
          (match uu____2959 with
           | (env,ps) -> (env, (PCons (cons, (FStar_List.rev ps)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____2995,ps) ->
          let uu____3005 =
            FStar_List.fold_left
              (fun uu____3018  ->
                 fun uu____3019  ->
                   match (uu____3018, uu____3019) with
                   | ((env,acc),(field,p)) ->
                       let uu____3056 = translate_pat env p  in
                       (match uu____3056 with
                        | (env,p) -> (env, ((field, p) :: acc)))) (env, [])
              ps
             in
          (match uu____3005 with
           | (env,ps) -> (env, (PRecord (FStar_List.rev ps))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____3507 =
            FStar_List.fold_left
              (fun uu____3097  ->
                 fun p  ->
                   match uu____3097 with
                   | (env,acc) ->
                       let uu____3109 = translate_pat env p  in
                       (match uu____3109 with | (env,p) -> (env, (p :: acc))))
              (env, []) ps
             in
          (match uu____3090 with
           | (env,ps) -> (env, (PTuple (FStar_List.rev ps))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____3125 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____3545 ->
          failwith "todo: translate_pat [MLP_Branch]"

and translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some uu____3552) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____3560 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3561 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____3562 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3563 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (uu____3565,None ) ->
        failwith "todo: translate_expr [MLC_Int]"

and mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          EApp
            (let _0_671 = FStar_List.map (translate_expr env) args  in
             ((EOp (op, w)), _0_671))
