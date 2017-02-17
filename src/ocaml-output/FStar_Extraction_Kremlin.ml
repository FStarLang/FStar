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
          names_t = (uu___146_1774.names_t);
          module_name = (uu___146_1774.module_name)
        }
  
let extend_t : env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___147_1781 = env  in
      {
        names = (uu___147_1781.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___147_1781.module_name)
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
  fun env  -> fun x  -> let uu____1798 = find_name env x  in uu____1798.mut 
let find : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      FStar_All.try_with
        (fun uu___149_1805  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
        (fun uu___148_1807  ->
           match uu___148_1807 with
           | uu____1808 ->
               let uu____1809 =
                 FStar_Util.format1 "Internal error: name not found %s\n" x
                  in
               failwith uu____1809)
  
let find_t : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      FStar_All.try_with
        (fun uu___151_1816  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t)
        (fun uu___150_1818  ->
           match uu___150_1818 with
           | uu____1819 ->
               let uu____1820 =
                 FStar_Util.format1 "Internal error: name not found %s\n" x
                  in
               failwith uu____1820)
  
let add_binders env binders =
  FStar_List.fold_left
    (fun env  ->
       fun uu____1850  ->
         match uu____1850 with
         | ((name,uu____1856),uu____1857) -> extend env name false) env
    binders
  
let rec translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____1948  ->
    match uu____1948 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____1979 = m  in
               match uu____1979 with
               | ((prefix,final),uu____1991,uu____1992) ->
                   FStar_String.concat "." (FStar_List.append prefix [final])
                in
             FStar_All.try_with
               (fun uu___153_2005  ->
                  match () with
                  | () ->
                      (FStar_Util.print1
                         "Attempting to translate module %s\n" m_name;
                       (let uu____2008 = translate_module m  in
                        Some uu____2008)))
               (fun uu___152_2009  ->
                  match uu___152_2009 with
                  | e ->
                      ((let uu____2013 = FStar_Util.print_exn e  in
                        FStar_Util.print2
                          "Unable to translate module: %s because:\n  %s\n"
                          m_name uu____2013);
                       None))) modules

and translate_module :
  ((Prims.string Prims.list * Prims.string) *
    (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule)
    Prims.option * FStar_Extraction_ML_Syntax.mllib) -> file
  =
  fun uu____2014  ->
    match uu____2014 with
    | (module_name,modul,uu____2026) ->
        let module_name =
          FStar_List.append (Prims.fst module_name) [Prims.snd module_name]
           in
        let program =
          match modul with
          | Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name))
                decls
          | uu____2050 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name), program)

and translate_flags :
  FStar_Extraction_ML_Syntax.c_flag Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___142_2058  ->
         match uu___142_2058 with
         | FStar_Extraction_ML_Syntax.Private  -> Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  -> Some NoExtract
         | FStar_Extraction_ML_Syntax.Attribute "c_inline" -> Some CInline
         | FStar_Extraction_ML_Syntax.Attribute "substitute" ->
             Some Substitute
         | FStar_Extraction_ML_Syntax.Attribute a ->
             (FStar_Util.print1_warning "Warning: unrecognized attribute %s"
                a;
              None)
         | uu____2062 -> None) flags

and translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.option =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
        (flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = (name,_);
                        FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t0);
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
                        FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t0);
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
              (fun uu___143_2110  ->
                 match uu___143_2110 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2111 -> false) flags
             in
          let env =
            match flavor = FStar_Extraction_ML_Syntax.Rec with
            | true  -> extend env name false
            | uu____2113 -> env  in
          let rec find_return_type uu___144_2117 =
            match uu___144_2117 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2118,uu____2119,t)
                -> find_return_type t
            | t -> t  in
          let t =
            let uu____2123 = find_return_type t0  in
            translate_type env uu____2123  in
          let binders = translate_binders env args  in
          let env = add_binders env args  in
          let name = ((env.module_name), name)  in
          let flags = translate_flags flags  in
          (match assumed with
           | true  ->
               let uu____2135 =
                 let uu____2136 =
                   let uu____2144 = translate_type env t0  in
                   (None, name, uu____2144)  in
                 DExternal uu____2136  in
               Some uu____2135
           | uu____2149 ->
               FStar_All.try_with
                 (fun uu___155_2151  ->
                    match () with
                    | () ->
                        let body = translate_expr env body  in
                        Some
                          (DFunction (None, flags, t, name, binders, body)))
                 (fun uu___154_2160  ->
                    match uu___154_2160 with
                    | e ->
                        ((let uu____2164 = FStar_Util.print_exn e  in
                          FStar_Util.print2
                            "Warning: writing a stub for %s (%s)\n"
                            (Prims.snd name) uu____2164);
                         Some
                           (DFunction (None, flags, t, name, binders, EAbort)))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2175);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2177;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2179;_}::[])
          ->
          let flags = translate_flags flags  in
          let t = translate_type env t  in
          let name = ((env.module_name), name)  in
          FStar_All.try_with
            (fun uu___157_2194  ->
               match () with
               | () ->
                   let expr = translate_expr env expr  in
                   Some (DGlobal (flags, name, t, expr)))
            (fun uu___156_2201  ->
               match uu___156_2201 with
               | e ->
                   ((let uu____2205 = FStar_Util.print_exn e  in
                     FStar_Util.print2
                       "Warning: not translating definition for %s (%s)\n"
                       (Prims.snd name) uu____2205);
                    Some (DGlobal (flags, name, t, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____2211,uu____2212,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____2214);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____2216;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____2217;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____2218;_}::uu____2219)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | Some (idents,t) ->
                let uu____2229 =
                  let uu____2230 = FStar_List.map Prims.fst idents  in
                  FStar_String.concat ", " uu____2230  in
                let uu____2234 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____2229 uu____2234
            | None  -> ());
           None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____2236 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____2238 -> None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2270  ->
                   match uu____2270 with
                   | (name,uu____2274) -> extend_t env name) env args
             in
          (match assumed with
           | true  -> None
           | uu____2276 ->
               let uu____2277 =
                 let uu____2278 =
                   let uu____2285 = translate_type env t  in
                   (name, (FStar_List.length args), uu____2285)  in
                 DTypeAlias uu____2278  in
               Some uu____2277)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2291,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2325  ->
                   match uu____2325 with
                   | (name,uu____2329) -> extend_t env name) env args
             in
          let uu____2330 =
            let uu____2331 =
              let uu____2343 =
                FStar_List.map
                  (fun uu____2355  ->
                     match uu____2355 with
                     | (f,t) ->
                         let uu____2364 =
                           let uu____2367 = translate_type env t  in
                           (uu____2367, false)  in
                         (f, uu____2364)) fields
                 in
              (name, (FStar_List.length args), uu____2343)  in
            DTypeFlat uu____2331  in
          Some uu____2330
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2380,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name = ((env.module_name), name)  in
          let env =
            FStar_List.fold_left
              (fun env  ->
                 fun uu____2415  ->
                   match uu____2415 with
                   | (name,uu____2419) -> extend_t env name) env args
             in
          let uu____2420 =
            let uu____2421 =
              let uu____2436 =
                FStar_List.mapi
                  (fun i  ->
                     fun uu____2456  ->
                       match uu____2456 with
                       | (cons,ts) ->
                           let uu____2471 =
                             FStar_List.mapi
                               (fun j  ->
                                  fun t  ->
                                    let uu____2483 =
                                      let uu____2484 =
                                        FStar_Util.string_of_int i  in
                                      let uu____2485 =
                                        FStar_Util.string_of_int j  in
                                      FStar_Util.format2 "x%s%s" uu____2484
                                        uu____2485
                                       in
                                    let uu____2486 =
                                      let uu____2489 = translate_type env t
                                         in
                                      (uu____2489, false)  in
                                    (uu____2483, uu____2486)) ts
                              in
                           (cons, uu____2471)) branches
                 in
              (name, (FStar_List.length args), uu____2436)  in
            DTypeVariant uu____2421  in
          Some uu____2420
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2510,name,_mangled_name,uu____2513,uu____2514)::uu____2515)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2537 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2539 ->
          failwith "todo: translate_decl [MLM_Exn]"

and translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple []
        |FStar_Extraction_ML_Syntax.MLTY_Top  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____2547) ->
          let uu____2548 = find_t env name  in TBound uu____2548
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2550,t2) ->
          let uu____2552 =
            let uu____2555 = translate_type env t1  in
            let uu____2556 = translate_type env t2  in
            (uu____2555, uu____2556)  in
          TArrow uu____2552
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2559 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2559 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2562 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2562 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____2569 = FStar_Util.must (mk_width m)  in TInt uu____2569
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____2576 = FStar_Util.must (mk_width m)  in TInt uu____2576
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____2580 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2580 = "FStar.Buffer.buffer" ->
          let uu____2581 = translate_type env arg  in TBuf uu____2581
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2582::[],p) when
          let uu____2585 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2585 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,("Prims"::[],t)) when
          FStar_Util.starts_with t "tuple" ->
          let uu____2603 = FStar_List.map (translate_type env) args  in
          TTuple uu____2603
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          (match (FStar_List.length args) > (Prims.parse_int "0") with
           | true  ->
               let uu____2612 =
                 let uu____2619 = FStar_List.map (translate_type env) args
                    in
                 (lid, uu____2619)  in
               TApp uu____2612
           | uu____2622 -> TQualified lid)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____2625 = FStar_List.map (translate_type env) ts  in
          TTuple uu____2625

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
    fun uu____2635  ->
      match uu____2635 with
      | ((name,uu____2639),typ) ->
          let uu____2643 = translate_type env typ  in
          { name; typ = uu____2643; mut = false }

and translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2648) ->
          let uu____2649 = find env name  in EBound uu____2649
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____2653 =
            let uu____2656 = FStar_Util.must (mk_op op)  in
            let uu____2657 = FStar_Util.must (mk_width m)  in
            (uu____2656, uu____2657)  in
          EOp uu____2653
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____2660 =
            let uu____2663 = FStar_Util.must (mk_bool_op op)  in
            (uu____2663, Bool)  in
          EOp uu____2660
      | FStar_Extraction_ML_Syntax.MLE_Name n -> EQualified n
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____2668);
                           FStar_Extraction_ML_Syntax.mllb_tysc = Some
                             ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___145_2684  ->
                 match uu___145_2684 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____2685 -> false) flags
             in
          let uu____2686 =
            match is_mut with
            | true  ->
                let uu____2691 =
                  match typ with
                  | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                      let uu____2695 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____2695 = "FStar.ST.stackref" -> t
                  | uu____2696 ->
                      let uu____2697 =
                        let uu____2698 =
                          FStar_Extraction_ML_Code.string_of_mlty ([], "")
                            typ
                           in
                        FStar_Util.format1
                          "unexpected: bad desugaring of Mutable (typ is %s)"
                          uu____2698
                         in
                      failwith uu____2697
                   in
                let uu____2700 =
                  match body with
                  | {
                      FStar_Extraction_ML_Syntax.expr =
                        FStar_Extraction_ML_Syntax.MLE_App
                        (uu____2701,body::[]);
                      FStar_Extraction_ML_Syntax.mlty = uu____2703;
                      FStar_Extraction_ML_Syntax.loc = uu____2704;_} -> body
                  | uu____2706 ->
                      failwith "unexpected: bad desugaring of Mutable"
                   in
                (uu____2691, uu____2700)
            | uu____2707 -> (typ, body)  in
          (match uu____2686 with
           | (typ,body) ->
               let binder =
                 let uu____2711 = translate_type env typ  in
                 { name; typ = uu____2711; mut = is_mut }  in
               let body = translate_expr env body  in
               let env = extend env name is_mut  in
               let continuation = translate_expr env continuation  in
               ELet (binder, body, continuation))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____2727 =
            let uu____2733 = translate_expr env expr  in
            let uu____2734 = translate_branches env branches  in
            (uu____2733, uu____2734)  in
          EMatch uu____2727
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2742;
             FStar_Extraction_ML_Syntax.loc = uu____2743;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v,uu____2745);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2746;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2747;_}::[])
          when
          (let uu____2749 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____2749 = "FStar.ST.op_Bang") && (is_mutable env v)
          -> let uu____2750 = find env v  in EBound uu____2750
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2752;
             FStar_Extraction_ML_Syntax.loc = uu____2753;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v,uu____2755);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2756;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2757;_}::e::[])
          when
          (let uu____2760 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____2760 = "FStar.ST.op_Colon_Equals") && (is_mutable env v)
          ->
          let uu____2761 =
            let uu____2764 =
              let uu____2765 = find env v  in EBound uu____2765  in
            let uu____2766 = translate_expr env e  in
            (uu____2764, uu____2766)  in
          EAssign uu____2761
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2768;
             FStar_Extraction_ML_Syntax.loc = uu____2769;_},e1::e2::[])
          when
          (let uu____2773 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____2773 = "FStar.Buffer.index") ||
            (let uu____2774 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____2774 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____2775 =
            let uu____2778 = translate_expr env e1  in
            let uu____2779 = translate_expr env e2  in
            (uu____2778, uu____2779)  in
          EBufRead uu____2775
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2781;
             FStar_Extraction_ML_Syntax.loc = uu____2782;_},e1::e2::[])
          when
          let uu____2786 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2786 = "FStar.Buffer.create" ->
          let uu____2787 =
            let uu____2791 = translate_expr env e1  in
            let uu____2792 = translate_expr env e2  in
            (Stack, uu____2791, uu____2792)  in
          EBufCreate uu____2787
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2794;
             FStar_Extraction_ML_Syntax.loc = uu____2795;_},_e0::e1::e2::[])
          when
          let uu____2800 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2800 = "FStar.Buffer.rcreate" ->
          let uu____2801 =
            let uu____2805 = translate_expr env e1  in
            let uu____2806 = translate_expr env e2  in
            (Eternal, uu____2805, uu____2806)  in
          EBufCreate uu____2801
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2808;
             FStar_Extraction_ML_Syntax.loc = uu____2809;_},e2::[])
          when
          let uu____2812 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2812 = "FStar.Buffer.createL" ->
          let rec list_elements acc e2 =
            match e2.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd::tl::[]) ->
                list_elements (hd :: acc) tl
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____2836 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!"
             in
          let list_elements = list_elements []  in
          let uu____2842 =
            let uu____2846 =
              let uu____2848 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____2848  in
            (Stack, uu____2846)  in
          EBufCreateL uu____2842
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2852;
             FStar_Extraction_ML_Syntax.loc = uu____2853;_},e1::e2::_e3::[])
          when
          let uu____2858 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2858 = "FStar.Buffer.sub" ->
          let uu____2859 =
            let uu____2862 = translate_expr env e1  in
            let uu____2863 = translate_expr env e2  in
            (uu____2862, uu____2863)  in
          EBufSub uu____2859
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2865;
             FStar_Extraction_ML_Syntax.loc = uu____2866;_},e1::e2::[])
          when
          let uu____2870 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2870 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2872;
             FStar_Extraction_ML_Syntax.loc = uu____2873;_},e1::e2::[])
          when
          let uu____2877 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2877 = "FStar.Buffer.offset" ->
          let uu____2878 =
            let uu____2881 = translate_expr env e1  in
            let uu____2882 = translate_expr env e2  in
            (uu____2881, uu____2882)  in
          EBufSub uu____2878
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2884;
             FStar_Extraction_ML_Syntax.loc = uu____2885;_},e1::e2::e3::[])
          when
          (let uu____2890 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____2890 = "FStar.Buffer.upd") ||
            (let uu____2891 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____2891 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____2892 =
            let uu____2896 = translate_expr env e1  in
            let uu____2897 = translate_expr env e2  in
            let uu____2898 = translate_expr env e3  in
            (uu____2896, uu____2897, uu____2898)  in
          EBufWrite uu____2892
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2900;
             FStar_Extraction_ML_Syntax.loc = uu____2901;_},uu____2902::[])
          when
          let uu____2904 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2904 = "FStar.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2906;
             FStar_Extraction_ML_Syntax.loc = uu____2907;_},uu____2908::[])
          when
          let uu____2910 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2910 = "FStar.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2912;
             FStar_Extraction_ML_Syntax.loc = uu____2913;_},e1::e2::e3::e4::e5::[])
          when
          let uu____2920 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2920 = "FStar.Buffer.blit" ->
          let uu____2921 =
            let uu____2927 = translate_expr env e1  in
            let uu____2928 = translate_expr env e2  in
            let uu____2929 = translate_expr env e3  in
            let uu____2930 = translate_expr env e4  in
            let uu____2931 = translate_expr env e5  in
            (uu____2927, uu____2928, uu____2929, uu____2930, uu____2931)  in
          EBufBlit uu____2921
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2933;
             FStar_Extraction_ML_Syntax.loc = uu____2934;_},e1::e2::e3::[])
          when
          let uu____2939 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2939 = "FStar.Buffer.fill" ->
          let uu____2940 =
            let uu____2944 = translate_expr env e1  in
            let uu____2945 = translate_expr env e2  in
            let uu____2946 = translate_expr env e3  in
            (uu____2944, uu____2945, uu____2946)  in
          EBufFill uu____2940
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2948;
             FStar_Extraction_ML_Syntax.loc = uu____2949;_},uu____2950::[])
          when
          let uu____2952 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2952 = "FStar.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2954;
             FStar_Extraction_ML_Syntax.loc = uu____2955;_},e::[])
          when
          let uu____2958 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____2958 = "Obj.repr" ->
          let uu____2959 =
            let uu____2962 = translate_expr env e  in (uu____2962, TAny)  in
          ECast uu____2959
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____2965;
             FStar_Extraction_ML_Syntax.loc = uu____2966;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____2971 = FStar_Util.must (mk_width m)  in
          let uu____2972 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____2971 uu____2972 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____2974;
             FStar_Extraction_ML_Syntax.loc = uu____2975;_},args)
          when is_bool_op op ->
          let uu____2980 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____2980 args
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
          let uu____3005 =
            let uu____3008 = FStar_Util.must (mk_width m)  in (uu____3008, c)
             in
          EConstant uu____3005
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____3009;
             FStar_Extraction_ML_Syntax.loc = uu____3010;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3012;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3013;_}::[])
          ->
          (match e with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____3017 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____3019;
             FStar_Extraction_ML_Syntax.loc = uu____3020;_},arg::[])
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
               let uu____3025 =
                 let uu____3028 = translate_expr env arg  in
                 (uu____3028, (TInt UInt64))  in
               ECast uu____3025
           | uu____3029 ->
               (match (FStar_Util.ends_with c "uint32") && is_known_type with
                | true  ->
                    let uu____3030 =
                      let uu____3033 = translate_expr env arg  in
                      (uu____3033, (TInt UInt32))  in
                    ECast uu____3030
                | uu____3034 ->
                    (match (FStar_Util.ends_with c "uint16") && is_known_type
                     with
                     | true  ->
                         let uu____3035 =
                           let uu____3038 = translate_expr env arg  in
                           (uu____3038, (TInt UInt16))  in
                         ECast uu____3035
                     | uu____3039 ->
                         (match (FStar_Util.ends_with c "uint8") &&
                                  is_known_type
                          with
                          | true  ->
                              let uu____3040 =
                                let uu____3043 = translate_expr env arg  in
                                (uu____3043, (TInt UInt8))  in
                              ECast uu____3040
                          | uu____3044 ->
                              (match (FStar_Util.ends_with c "int64") &&
                                       is_known_type
                               with
                               | true  ->
                                   let uu____3045 =
                                     let uu____3048 = translate_expr env arg
                                        in
                                     (uu____3048, (TInt Int64))  in
                                   ECast uu____3045
                               | uu____3049 ->
                                   (match (FStar_Util.ends_with c "int32") &&
                                            is_known_type
                                    with
                                    | true  ->
                                        let uu____3050 =
                                          let uu____3053 =
                                            translate_expr env arg  in
                                          (uu____3053, (TInt Int32))  in
                                        ECast uu____3050
                                    | uu____3054 ->
                                        (match (FStar_Util.ends_with c
                                                  "int16")
                                                 && is_known_type
                                         with
                                         | true  ->
                                             let uu____3055 =
                                               let uu____3058 =
                                                 translate_expr env arg  in
                                               (uu____3058, (TInt Int16))  in
                                             ECast uu____3055
                                         | uu____3059 ->
                                             (match (FStar_Util.ends_with c
                                                       "int8")
                                                      && is_known_type
                                              with
                                              | true  ->
                                                  let uu____3060 =
                                                    let uu____3063 =
                                                      translate_expr env arg
                                                       in
                                                    (uu____3063, (TInt Int8))
                                                     in
                                                  ECast uu____3060
                                              | uu____3064 ->
                                                  let uu____3065 =
                                                    let uu____3069 =
                                                      let uu____3071 =
                                                        translate_expr env
                                                          arg
                                                         in
                                                      [uu____3071]  in
                                                    ((EQualified
                                                        (["FStar";
                                                         "Int";
                                                         "Cast"], c)),
                                                      uu____3069)
                                                     in
                                                  EApp uu____3065))))))))
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____3076;
             FStar_Extraction_ML_Syntax.loc = uu____3077;_},args)
          ->
          let uu____3083 =
            let uu____3087 = FStar_List.map (translate_expr env) args  in
            ((EQualified (path, function_name)), uu____3087)  in
          EApp uu____3083
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e,t_from,t_to) ->
          let uu____3094 =
            let uu____3097 = translate_expr env e  in
            let uu____3098 = translate_type env t_to  in
            (uu____3097, uu____3098)  in
          ECast uu____3094
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____3099,fields) ->
          let uu____3109 =
            let uu____3115 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____3116 =
              FStar_List.map
                (fun uu____3124  ->
                   match uu____3124 with
                   | (field,expr) ->
                       let uu____3131 = translate_expr env expr  in
                       (field, uu____3131)) fields
               in
            (uu____3115, uu____3116)  in
          EFlat uu____3109
      | FStar_Extraction_ML_Syntax.MLE_Proj (e,path) ->
          let uu____3137 =
            let uu____3141 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____3142 = translate_expr env e  in
            (uu____3141, uu____3142, (Prims.snd path))  in
          EField uu____3137
      | FStar_Extraction_ML_Syntax.MLE_Let uu____3144 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head,uu____3152) ->
          let uu____3155 =
            let uu____3156 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____3156
             in
          failwith uu____3155
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____3160 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____3160
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____3164 = FStar_List.map (translate_expr env) es  in
          ETuple uu____3164
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3166,cons),es) ->
          let uu____3176 =
            let uu____3181 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____3182 = FStar_List.map (translate_expr env) es  in
            (uu____3181, cons, uu____3182)  in
          ECons uu____3176
      | FStar_Extraction_ML_Syntax.MLE_Fun uu____3185 ->
          failwith "todo: translate_expr [MLE_Fun]"
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____3196 =
            let uu____3200 = translate_expr env e1  in
            let uu____3201 = translate_expr env e2  in
            let uu____3202 =
              match e3 with
              | None  -> EUnit
              | Some e3 -> translate_expr env e3  in
            (uu____3200, uu____3201, uu____3202)  in
          EIfThenElse uu____3196
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____3204 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____3208 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____3216 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          (match (FStar_List.length ts) > (Prims.parse_int "0") with
           | true  ->
               let uu____3229 =
                 let uu____3236 = FStar_List.map (translate_type env) ts  in
                 (lid, uu____3236)  in
               TApp uu____3229
           | uu____3239 -> TQualified lid)
      | uu____3240 -> failwith "invalid argument: assert_lid"

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
    fun uu____3255  ->
      match uu____3255 with
      | (pat,guard,expr) ->
          (match guard = None with
           | true  ->
               let uu____3270 = translate_pat env pat  in
               (match uu____3270 with
                | (env,pat) ->
                    let uu____3277 = translate_expr env expr  in
                    (pat, uu____3277))
           | uu____3278 -> failwith "todo: translate_branch")

and translate_pat :
  env -> FStar_Extraction_ML_Syntax.mlpattern -> (env * pattern) =
  fun env  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____3287) ->
          let env = extend env name false  in
          (env, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env = extend env "_" false  in
          (env, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3290,cons),ps) ->
          let uu____3300 =
            FStar_List.fold_left
              (fun uu____3307  ->
                 fun p  ->
                   match uu____3307 with
                   | (env,acc) ->
                       let uu____3319 = translate_pat env p  in
                       (match uu____3319 with | (env,p) -> (env, (p :: acc))))
              (env, []) ps
             in
          (match uu____3300 with
           | (env,ps) -> (env, (PCons (cons, (FStar_List.rev ps)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____3336,ps) ->
          let uu____3346 =
            FStar_List.fold_left
              (fun uu____3359  ->
                 fun uu____3360  ->
                   match (uu____3359, uu____3360) with
                   | ((env,acc),(field,p)) ->
                       let uu____3397 = translate_pat env p  in
                       (match uu____3397 with
                        | (env,p) -> (env, ((field, p) :: acc)))) (env, [])
              ps
             in
          (match uu____3346 with
           | (env,ps) -> (env, (PRecord (FStar_List.rev ps))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____3431 =
            FStar_List.fold_left
              (fun uu____3438  ->
                 fun p  ->
                   match uu____3438 with
                   | (env,acc) ->
                       let uu____3450 = translate_pat env p  in
                       (match uu____3450 with | (env,p) -> (env, (p :: acc))))
              (env, []) ps
             in
          (match uu____3431 with
           | (env,ps) -> (env, (PTuple (FStar_List.rev ps))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____3466 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____3469 ->
          failwith "todo: translate_pat [MLP_Branch]"

and translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some uu____3476) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____3484 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3485 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____3486 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3487 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (uu____3489,None ) ->
        failwith "todo: translate_expr [MLC_Int]"

and mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____3500 =
            let uu____3504 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____3504)  in
          EApp uu____3500
