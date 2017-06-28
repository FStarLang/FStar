
open Prims
open FStar_Pervasives
type decl =
| DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) * typ * expr)
| DFunction of (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ * (Prims.string Prims.list * Prims.string) * binder Prims.list * expr)
| DTypeAlias of ((Prims.string Prims.list * Prims.string) * Prims.int * typ)
| DTypeFlat of ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list)
| DExternal of (cc FStar_Pervasives_Native.option * (Prims.string Prims.list * Prims.string) * typ)
| DTypeVariant of ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list) 
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
 and binder =
{name : Prims.string; typ : typ; mut : Prims.bool} 
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


let uu___is_DGlobal : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DGlobal (_0) -> begin
true
end
| uu____349 -> begin
false
end))


let __proj__DGlobal__item___0 : decl  ->  (flag Prims.list * (Prims.string Prims.list * Prims.string) * typ * expr) = (fun projectee -> (match (projectee) with
| DGlobal (_0) -> begin
_0
end))


let uu___is_DFunction : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DFunction (_0) -> begin
true
end
| uu____400 -> begin
false
end))


let __proj__DFunction__item___0 : decl  ->  (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ * (Prims.string Prims.list * Prims.string) * binder Prims.list * expr) = (fun projectee -> (match (projectee) with
| DFunction (_0) -> begin
_0
end))


let uu___is_DTypeAlias : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeAlias (_0) -> begin
true
end
| uu____459 -> begin
false
end))


let __proj__DTypeAlias__item___0 : decl  ->  ((Prims.string Prims.list * Prims.string) * Prims.int * typ) = (fun projectee -> (match (projectee) with
| DTypeAlias (_0) -> begin
_0
end))


let uu___is_DTypeFlat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeFlat (_0) -> begin
true
end
| uu____502 -> begin
false
end))


let __proj__DTypeFlat__item___0 : decl  ->  ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list) = (fun projectee -> (match (projectee) with
| DTypeFlat (_0) -> begin
_0
end))


let uu___is_DExternal : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DExternal (_0) -> begin
true
end
| uu____556 -> begin
false
end))


let __proj__DExternal__item___0 : decl  ->  (cc FStar_Pervasives_Native.option * (Prims.string Prims.list * Prims.string) * typ) = (fun projectee -> (match (projectee) with
| DExternal (_0) -> begin
_0
end))


let uu___is_DTypeVariant : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeVariant (_0) -> begin
true
end
| uu____605 -> begin
false
end))


let __proj__DTypeVariant__item___0 : decl  ->  ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list) = (fun projectee -> (match (projectee) with
| DTypeVariant (_0) -> begin
_0
end))


let uu___is_StdCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| StdCall -> begin
true
end
| uu____660 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____665 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____670 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____675 -> begin
false
end))


let uu___is_NoExtract : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____680 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____685 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____690 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____695 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____700 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____706 -> begin
false
end))


let __proj__EBound__item___0 : expr  ->  Prims.int = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
_0
end))


let uu___is_EQualified : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EQualified (_0) -> begin
true
end
| uu____723 -> begin
false
end))


let __proj__EQualified__item___0 : expr  ->  (Prims.string Prims.list * Prims.string) = (fun projectee -> (match (projectee) with
| EQualified (_0) -> begin
_0
end))


let uu___is_EConstant : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EConstant (_0) -> begin
true
end
| uu____748 -> begin
false
end))


let __proj__EConstant__item___0 : expr  ->  (width * Prims.string) = (fun projectee -> (match (projectee) with
| EConstant (_0) -> begin
_0
end))


let uu___is_EUnit : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EUnit -> begin
true
end
| uu____767 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____776 -> begin
false
end))


let __proj__EApp__item___0 : expr  ->  (expr * expr Prims.list) = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
_0
end))


let uu___is_ELet : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ELet (_0) -> begin
true
end
| uu____802 -> begin
false
end))


let __proj__ELet__item___0 : expr  ->  (binder * expr * expr) = (fun projectee -> (match (projectee) with
| ELet (_0) -> begin
_0
end))


let uu___is_EIfThenElse : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EIfThenElse (_0) -> begin
true
end
| uu____828 -> begin
false
end))


let __proj__EIfThenElse__item___0 : expr  ->  (expr * expr * expr) = (fun projectee -> (match (projectee) with
| EIfThenElse (_0) -> begin
_0
end))


let uu___is_ESequence : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ESequence (_0) -> begin
true
end
| uu____852 -> begin
false
end))


let __proj__ESequence__item___0 : expr  ->  expr Prims.list = (fun projectee -> (match (projectee) with
| ESequence (_0) -> begin
_0
end))


let uu___is_EAssign : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAssign (_0) -> begin
true
end
| uu____871 -> begin
false
end))


let __proj__EAssign__item___0 : expr  ->  (expr * expr) = (fun projectee -> (match (projectee) with
| EAssign (_0) -> begin
_0
end))


let uu___is_EBufCreate : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufCreate (_0) -> begin
true
end
| uu____894 -> begin
false
end))


let __proj__EBufCreate__item___0 : expr  ->  (lifetime * expr * expr) = (fun projectee -> (match (projectee) with
| EBufCreate (_0) -> begin
_0
end))


let uu___is_EBufRead : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufRead (_0) -> begin
true
end
| uu____919 -> begin
false
end))


let __proj__EBufRead__item___0 : expr  ->  (expr * expr) = (fun projectee -> (match (projectee) with
| EBufRead (_0) -> begin
_0
end))


let uu___is_EBufWrite : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufWrite (_0) -> begin
true
end
| uu____942 -> begin
false
end))


let __proj__EBufWrite__item___0 : expr  ->  (expr * expr * expr) = (fun projectee -> (match (projectee) with
| EBufWrite (_0) -> begin
_0
end))


let uu___is_EBufSub : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufSub (_0) -> begin
true
end
| uu____967 -> begin
false
end))


let __proj__EBufSub__item___0 : expr  ->  (expr * expr) = (fun projectee -> (match (projectee) with
| EBufSub (_0) -> begin
_0
end))


let uu___is_EBufBlit : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufBlit (_0) -> begin
true
end
| uu____992 -> begin
false
end))


let __proj__EBufBlit__item___0 : expr  ->  (expr * expr * expr * expr * expr) = (fun projectee -> (match (projectee) with
| EBufBlit (_0) -> begin
_0
end))


let uu___is_EMatch : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EMatch (_0) -> begin
true
end
| uu____1026 -> begin
false
end))


let __proj__EMatch__item___0 : expr  ->  (expr * (pattern * expr) Prims.list) = (fun projectee -> (match (projectee) with
| EMatch (_0) -> begin
_0
end))


let uu___is_EOp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EOp (_0) -> begin
true
end
| uu____1057 -> begin
false
end))


let __proj__EOp__item___0 : expr  ->  (op * width) = (fun projectee -> (match (projectee) with
| EOp (_0) -> begin
_0
end))


let uu___is_ECast : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ECast (_0) -> begin
true
end
| uu____1079 -> begin
false
end))


let __proj__ECast__item___0 : expr  ->  (expr * typ) = (fun projectee -> (match (projectee) with
| ECast (_0) -> begin
_0
end))


let uu___is_EPushFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPushFrame -> begin
true
end
| uu____1098 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____1103 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____1109 -> begin
false
end))


let __proj__EBool__item___0 : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
_0
end))


let uu___is_EAny : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAny -> begin
true
end
| uu____1122 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____1127 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____1133 -> begin
false
end))


let __proj__EReturn__item___0 : expr  ->  expr = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
_0
end))


let uu___is_EFlat : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EFlat (_0) -> begin
true
end
| uu____1152 -> begin
false
end))


let __proj__EFlat__item___0 : expr  ->  (typ * (Prims.string * expr) Prims.list) = (fun projectee -> (match (projectee) with
| EFlat (_0) -> begin
_0
end))


let uu___is_EField : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EField (_0) -> begin
true
end
| uu____1184 -> begin
false
end))


let __proj__EField__item___0 : expr  ->  (typ * expr * Prims.string) = (fun projectee -> (match (projectee) with
| EField (_0) -> begin
_0
end))


let uu___is_EWhile : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EWhile (_0) -> begin
true
end
| uu____1209 -> begin
false
end))


let __proj__EWhile__item___0 : expr  ->  (expr * expr) = (fun projectee -> (match (projectee) with
| EWhile (_0) -> begin
_0
end))


let uu___is_EBufCreateL : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufCreateL (_0) -> begin
true
end
| uu____1232 -> begin
false
end))


let __proj__EBufCreateL__item___0 : expr  ->  (lifetime * expr Prims.list) = (fun projectee -> (match (projectee) with
| EBufCreateL (_0) -> begin
_0
end))


let uu___is_ETuple : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ETuple (_0) -> begin
true
end
| uu____1256 -> begin
false
end))


let __proj__ETuple__item___0 : expr  ->  expr Prims.list = (fun projectee -> (match (projectee) with
| ETuple (_0) -> begin
_0
end))


let uu___is_ECons : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ECons (_0) -> begin
true
end
| uu____1277 -> begin
false
end))


let __proj__ECons__item___0 : expr  ->  (typ * Prims.string * expr Prims.list) = (fun projectee -> (match (projectee) with
| ECons (_0) -> begin
_0
end))


let uu___is_EBufFill : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufFill (_0) -> begin
true
end
| uu____1306 -> begin
false
end))


let __proj__EBufFill__item___0 : expr  ->  (expr * expr * expr) = (fun projectee -> (match (projectee) with
| EBufFill (_0) -> begin
_0
end))


let uu___is_EString : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EString (_0) -> begin
true
end
| uu____1329 -> begin
false
end))


let __proj__EString__item___0 : expr  ->  Prims.string = (fun projectee -> (match (projectee) with
| EString (_0) -> begin
_0
end))


let uu___is_EFun : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EFun (_0) -> begin
true
end
| uu____1346 -> begin
false
end))


let __proj__EFun__item___0 : expr  ->  (binder Prims.list * expr) = (fun projectee -> (match (projectee) with
| EFun (_0) -> begin
_0
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____1368 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____1373 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____1378 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____1383 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____1388 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____1393 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____1398 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____1403 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____1408 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____1413 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____1418 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____1423 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____1428 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____1433 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____1438 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____1443 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____1448 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____1453 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____1458 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____1463 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____1468 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____1473 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____1478 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____1483 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____1488 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____1493 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____1499 -> begin
false
end))


let __proj__PBool__item___0 : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
_0
end))


let uu___is_PVar : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PVar (_0) -> begin
true
end
| uu____1513 -> begin
false
end))


let __proj__PVar__item___0 : pattern  ->  binder = (fun projectee -> (match (projectee) with
| PVar (_0) -> begin
_0
end))


let uu___is_PCons : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PCons (_0) -> begin
true
end
| uu____1530 -> begin
false
end))


let __proj__PCons__item___0 : pattern  ->  (Prims.string * pattern Prims.list) = (fun projectee -> (match (projectee) with
| PCons (_0) -> begin
_0
end))


let uu___is_PTuple : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PTuple (_0) -> begin
true
end
| uu____1554 -> begin
false
end))


let __proj__PTuple__item___0 : pattern  ->  pattern Prims.list = (fun projectee -> (match (projectee) with
| PTuple (_0) -> begin
_0
end))


let uu___is_PRecord : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PRecord (_0) -> begin
true
end
| uu____1574 -> begin
false
end))


let __proj__PRecord__item___0 : pattern  ->  (Prims.string * pattern) Prims.list = (fun projectee -> (match (projectee) with
| PRecord (_0) -> begin
_0
end))


let uu___is_UInt8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt8 -> begin
true
end
| uu____1596 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____1601 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____1606 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____1611 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____1616 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____1621 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____1626 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____1631 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____1636 -> begin
false
end))


let uu___is_Int : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int -> begin
true
end
| uu____1641 -> begin
false
end))


let uu___is_UInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt -> begin
true
end
| uu____1646 -> begin
false
end))


let __proj__Mkbinder__item__name : binder  ->  Prims.string = (fun projectee -> (match (projectee) with
| {name = __fname__name; typ = __fname__typ; mut = __fname__mut} -> begin
__fname__name
end))


let __proj__Mkbinder__item__typ : binder  ->  typ = (fun projectee -> (match (projectee) with
| {name = __fname__name; typ = __fname__typ; mut = __fname__mut} -> begin
__fname__typ
end))


let __proj__Mkbinder__item__mut : binder  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; typ = __fname__typ; mut = __fname__mut} -> begin
__fname__mut
end))


let uu___is_TInt : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TInt (_0) -> begin
true
end
| uu____1673 -> begin
false
end))


let __proj__TInt__item___0 : typ  ->  width = (fun projectee -> (match (projectee) with
| TInt (_0) -> begin
_0
end))


let uu___is_TBuf : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBuf (_0) -> begin
true
end
| uu____1687 -> begin
false
end))


let __proj__TBuf__item___0 : typ  ->  typ = (fun projectee -> (match (projectee) with
| TBuf (_0) -> begin
_0
end))


let uu___is_TUnit : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TUnit -> begin
true
end
| uu____1700 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____1709 -> begin
false
end))


let __proj__TQualified__item___0 : typ  ->  (Prims.string Prims.list * Prims.string) = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
_0
end))


let uu___is_TBool : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBool -> begin
true
end
| uu____1731 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____1736 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____1744 -> begin
false
end))


let __proj__TArrow__item___0 : typ  ->  (typ * typ) = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
_0
end))


let uu___is_TZ : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TZ -> begin
true
end
| uu____1763 -> begin
false
end))


let uu___is_TBound : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
true
end
| uu____1769 -> begin
false
end))


let __proj__TBound__item___0 : typ  ->  Prims.int = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
_0
end))


let uu___is_TApp : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TApp (_0) -> begin
true
end
| uu____1789 -> begin
false
end))


let __proj__TApp__item___0 : typ  ->  ((Prims.string Prims.list * Prims.string) * typ Prims.list) = (fun projectee -> (match (projectee) with
| TApp (_0) -> begin
_0
end))


let uu___is_TTuple : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TTuple (_0) -> begin
true
end
| uu____1822 -> begin
false
end))


let __proj__TTuple__item___0 : typ  ->  typ Prims.list = (fun projectee -> (match (projectee) with
| TTuple (_0) -> begin
_0
end))


type program =
decl Prims.list


type ident =
Prims.string


type fields_t =
(Prims.string * (typ * Prims.bool)) Prims.list


type branches_t =
(Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list


type branch =
(pattern * expr)


type branches =
(pattern * expr) Prims.list


type constant =
(width * Prims.string)


type var =
Prims.int


type lident =
(Prims.string Prims.list * Prims.string)


type version =
Prims.int


let current_version : version = (Prims.parse_int "20")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun uu____1880 -> (match (uu____1880) with
| (x, uu____1885, uu____1886) -> begin
x
end))


let snd3 = (fun uu____1904 -> (match (uu____1904) with
| (uu____1908, x, uu____1910) -> begin
x
end))


let thd3 = (fun uu____1928 -> (match (uu____1928) with
| (uu____1932, uu____1933, x) -> begin
x
end))


let mk_width : Prims.string  ->  width FStar_Pervasives_Native.option = (fun uu___119_1939 -> (match (uu___119_1939) with
| "UInt8" -> begin
FStar_Pervasives_Native.Some (UInt8)
end
| "UInt16" -> begin
FStar_Pervasives_Native.Some (UInt16)
end
| "UInt32" -> begin
FStar_Pervasives_Native.Some (UInt32)
end
| "UInt64" -> begin
FStar_Pervasives_Native.Some (UInt64)
end
| "Int8" -> begin
FStar_Pervasives_Native.Some (Int8)
end
| "Int16" -> begin
FStar_Pervasives_Native.Some (Int16)
end
| "Int32" -> begin
FStar_Pervasives_Native.Some (Int32)
end
| "Int64" -> begin
FStar_Pervasives_Native.Some (Int64)
end
| uu____1941 -> begin
FStar_Pervasives_Native.None
end))


let mk_bool_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___120_1946 -> (match (uu___120_1946) with
| "op_Negation" -> begin
FStar_Pervasives_Native.Some (Not)
end
| "op_AmpAmp" -> begin
FStar_Pervasives_Native.Some (And)
end
| "op_BarBar" -> begin
FStar_Pervasives_Native.Some (Or)
end
| "op_Equality" -> begin
FStar_Pervasives_Native.Some (Eq)
end
| "op_disEquality" -> begin
FStar_Pervasives_Native.Some (Neq)
end
| uu____1948 -> begin
FStar_Pervasives_Native.None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> FStar_Pervasives_Native.None))


let mk_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___121_1958 -> (match (uu___121_1958) with
| "add" -> begin
FStar_Pervasives_Native.Some (Add)
end
| "op_Plus_Hat" -> begin
FStar_Pervasives_Native.Some (Add)
end
| "add_mod" -> begin
FStar_Pervasives_Native.Some (AddW)
end
| "op_Plus_Percent_Hat" -> begin
FStar_Pervasives_Native.Some (AddW)
end
| "sub" -> begin
FStar_Pervasives_Native.Some (Sub)
end
| "op_Subtraction_Hat" -> begin
FStar_Pervasives_Native.Some (Sub)
end
| "sub_mod" -> begin
FStar_Pervasives_Native.Some (SubW)
end
| "op_Subtraction_Percent_Hat" -> begin
FStar_Pervasives_Native.Some (SubW)
end
| "mul" -> begin
FStar_Pervasives_Native.Some (Mult)
end
| "op_Star_Hat" -> begin
FStar_Pervasives_Native.Some (Mult)
end
| "mul_mod" -> begin
FStar_Pervasives_Native.Some (MultW)
end
| "op_Star_Percent_Hat" -> begin
FStar_Pervasives_Native.Some (MultW)
end
| "div" -> begin
FStar_Pervasives_Native.Some (Div)
end
| "op_Slash_Hat" -> begin
FStar_Pervasives_Native.Some (Div)
end
| "div_mod" -> begin
FStar_Pervasives_Native.Some (DivW)
end
| "op_Slash_Percent_Hat" -> begin
FStar_Pervasives_Native.Some (DivW)
end
| "rem" -> begin
FStar_Pervasives_Native.Some (Mod)
end
| "op_Percent_Hat" -> begin
FStar_Pervasives_Native.Some (Mod)
end
| "logor" -> begin
FStar_Pervasives_Native.Some (BOr)
end
| "op_Bar_Hat" -> begin
FStar_Pervasives_Native.Some (BOr)
end
| "logxor" -> begin
FStar_Pervasives_Native.Some (BXor)
end
| "op_Hat_Hat" -> begin
FStar_Pervasives_Native.Some (BXor)
end
| "logand" -> begin
FStar_Pervasives_Native.Some (BAnd)
end
| "op_Amp_Hat" -> begin
FStar_Pervasives_Native.Some (BAnd)
end
| "lognot" -> begin
FStar_Pervasives_Native.Some (BNot)
end
| "shift_right" -> begin
FStar_Pervasives_Native.Some (BShiftR)
end
| "op_Greater_Greater_Hat" -> begin
FStar_Pervasives_Native.Some (BShiftR)
end
| "shift_left" -> begin
FStar_Pervasives_Native.Some (BShiftL)
end
| "op_Less_Less_Hat" -> begin
FStar_Pervasives_Native.Some (BShiftL)
end
| "eq" -> begin
FStar_Pervasives_Native.Some (Eq)
end
| "op_Equals_Hat" -> begin
FStar_Pervasives_Native.Some (Eq)
end
| "op_Greater_Hat" -> begin
FStar_Pervasives_Native.Some (Gt)
end
| "gt" -> begin
FStar_Pervasives_Native.Some (Gt)
end
| "op_Greater_Equals_Hat" -> begin
FStar_Pervasives_Native.Some (Gte)
end
| "gte" -> begin
FStar_Pervasives_Native.Some (Gte)
end
| "op_Less_Hat" -> begin
FStar_Pervasives_Native.Some (Lt)
end
| "lt" -> begin
FStar_Pervasives_Native.Some (Lt)
end
| "op_Less_Equals_Hat" -> begin
FStar_Pervasives_Native.Some (Lte)
end
| "lte" -> begin
FStar_Pervasives_Native.Some (Lte)
end
| uu____1960 -> begin
FStar_Pervasives_Native.None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> FStar_Pervasives_Native.None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> FStar_Pervasives_Native.None))

type env =
{names : name Prims.list; names_t : Prims.string Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let __proj__Mkenv__item__names : env  ->  name Prims.list = (fun projectee -> (match (projectee) with
| {names = __fname__names; names_t = __fname__names_t; module_name = __fname__module_name} -> begin
__fname__names
end))


let __proj__Mkenv__item__names_t : env  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {names = __fname__names; names_t = __fname__names_t; module_name = __fname__module_name} -> begin
__fname__names_t
end))


let __proj__Mkenv__item__module_name : env  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {names = __fname__names; names_t = __fname__names_t; module_name = __fname__module_name} -> begin
__fname__module_name
end))


let __proj__Mkname__item__pretty : name  ->  Prims.string = (fun projectee -> (match (projectee) with
| {pretty = __fname__pretty; mut = __fname__mut} -> begin
__fname__pretty
end))


let __proj__Mkname__item__mut : name  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {pretty = __fname__pretty; mut = __fname__mut} -> begin
__fname__mut
end))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; names_t = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let uu___126_2060 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = uu___126_2060.names_t; module_name = uu___126_2060.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___127_2069 = env
in {names = uu___127_2069.names; names_t = (x)::env.names_t; module_name = uu___127_2069.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____2078 = (FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)
in (match (uu____2078) with
| FStar_Pervasives_Native.Some (name) -> begin
name
end
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: name not found")
end)))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (

let uu____2091 = (find_name env x)
in uu____2091.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| uu____2108 -> begin
(

let uu____2109 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____2109))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| uu____2126 -> begin
(

let uu____2127 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____2127))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env1 uu____2166 -> (match (uu____2166) with
| ((name, uu____2172), uu____2173) -> begin
(extend env1 name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____2264 -> (match (uu____2264) with
| FStar_Extraction_ML_Syntax.MLLib (modules1) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____2297 = m
in (match (uu____2297) with
| ((prefix1, final), uu____2309, uu____2310) -> begin
(FStar_String.concat "." (FStar_List.append prefix1 ((final)::[])))
end))
in try
(match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
(

let uu____2329 = (translate_module m)
in FStar_Pervasives_Native.Some (uu____2329));
)
end)
with
| e -> begin
((

let uu____2337 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____2337));
FStar_Pervasives_Native.None;
)
end)) modules1)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____2338 -> (match (uu____2338) with
| (module_name, modul, uu____2350) -> begin
(

let module_name1 = (FStar_List.append (FStar_Pervasives_Native.fst module_name) (((FStar_Pervasives_Native.snd module_name))::[]))
in (

let program = (match (modul) with
| FStar_Pervasives_Native.Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name1)) decls)
end
| uu____2374 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name1)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun uu___122_2383 -> (match (uu___122_2383) with
| FStar_Extraction_ML_Syntax.Private -> begin
FStar_Pervasives_Native.Some (Private)
end
| FStar_Extraction_ML_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (NoExtract)
end
| FStar_Extraction_ML_Syntax.Attribute ("c_inline") -> begin
FStar_Pervasives_Native.Some (CInline)
end
| FStar_Extraction_ML_Syntax.Attribute ("substitute") -> begin
FStar_Pervasives_Native.Some (Substitute)
end
| FStar_Extraction_ML_Syntax.Attribute (a) -> begin
((FStar_Util.print1_warning "Warning: unrecognized attribute %s" a);
FStar_Pervasives_Native.None;
)
end
| uu____2387 -> begin
FStar_Pervasives_Native.None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl FStar_Pervasives_Native.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2394); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2397; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____2400; FStar_Extraction_ML_Syntax.loc = uu____2401}; FStar_Extraction_ML_Syntax.print_typ = uu____2402})::[]) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___123_2414 -> (match (uu___123_2414) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____2415 -> begin
false
end)) flags)
in (

let env1 = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____2417 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 uu____2426 -> (match (uu____2426) with
| (name1, uu____2430) -> begin
(extend_t env2 name1)
end)) env1 tvars)
in (

let rec find_return_type = (fun uu___124_2434 -> (match (uu___124_2434) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2435, uu____2436, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (

let uu____2440 = (find_return_type t0)
in (translate_type env2 uu____2440))
in (

let binders = (translate_binders env2 args)
in (

let env3 = (add_binders env2 args)
in (

let name1 = ((env3.module_name), (name))
in (

let flags1 = (translate_flags flags)
in (match (assumed) with
| true -> begin
(match (((FStar_List.length tvars) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2457 = (

let uu____2458 = (

let uu____2466 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (name1), (uu____2466)))
in DExternal (uu____2458))
in FStar_Pervasives_Native.Some (uu____2457))
end
| uu____2471 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____2472 -> begin
try
(match (()) with
| () -> begin
(

let body1 = (translate_expr env3 body)
in FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (body1)))))
end)
with
| e -> begin
((

let uu____2496 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____2496));
FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (EAbort))));
)
end
end))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2511); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2514; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____2517; FStar_Extraction_ML_Syntax.loc = uu____2518}, uu____2519, uu____2520); FStar_Extraction_ML_Syntax.mlty = uu____2521; FStar_Extraction_ML_Syntax.loc = uu____2522}; FStar_Extraction_ML_Syntax.print_typ = uu____2523})::[]) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___123_2535 -> (match (uu___123_2535) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____2536 -> begin
false
end)) flags)
in (

let env1 = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____2538 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 uu____2547 -> (match (uu____2547) with
| (name1, uu____2551) -> begin
(extend_t env2 name1)
end)) env1 tvars)
in (

let rec find_return_type = (fun uu___124_2555 -> (match (uu___124_2555) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2556, uu____2557, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (

let uu____2561 = (find_return_type t0)
in (translate_type env2 uu____2561))
in (

let binders = (translate_binders env2 args)
in (

let env3 = (add_binders env2 args)
in (

let name1 = ((env3.module_name), (name))
in (

let flags1 = (translate_flags flags)
in (match (assumed) with
| true -> begin
(match (((FStar_List.length tvars) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2578 = (

let uu____2579 = (

let uu____2587 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (name1), (uu____2587)))
in DExternal (uu____2579))
in FStar_Pervasives_Native.Some (uu____2578))
end
| uu____2592 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____2593 -> begin
try
(match (()) with
| () -> begin
(

let body1 = (translate_expr env3 body)
in FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (body1)))))
end)
with
| e -> begin
((

let uu____2617 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____2617));
FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (EAbort))));
)
end
end))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2632); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2634; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = uu____2636})::[]) -> begin
(

let flags1 = (translate_flags flags)
in (

let t1 = (translate_type env t)
in (

let name1 = ((env.module_name), (name))
in try
(match (()) with
| () -> begin
(

let expr1 = (translate_expr env expr)
in FStar_Pervasives_Native.Some (DGlobal (((flags1), (name1), (t1), (expr1)))))
end)
with
| e -> begin
((

let uu____2667 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____2667));
FStar_Pervasives_Native.Some (DGlobal (((flags1), (name1), (t1), (EAny))));
)
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2673, uu____2674, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2676); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2678; FStar_Extraction_ML_Syntax.mllb_def = uu____2679; FStar_Extraction_ML_Syntax.print_typ = uu____2680})::uu____2681) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
(match (ts) with
| FStar_Pervasives_Native.Some (idents, t) -> begin
(

let uu____2691 = (

let uu____2692 = (FStar_List.map FStar_Pervasives_Native.fst idents)
in (FStar_String.concat ", " uu____2692))
in (

let uu____2696 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" uu____2691 uu____2696)))
end
| FStar_Pervasives_Native.None -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2698) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2700) -> begin
FStar_Pervasives_Native.None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2736 -> (match (uu____2736) with
| (name2, uu____2740) -> begin
(extend_t env1 name2)
end)) env args)
in (match (assumed) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2742 -> begin
(

let uu____2743 = (

let uu____2744 = (

let uu____2751 = (translate_type env1 t)
in ((name1), ((FStar_List.length args)), (uu____2751)))
in DTypeAlias (uu____2744))
in FStar_Pervasives_Native.Some (uu____2743))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2759, name, _mangled_name, args, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2797 -> (match (uu____2797) with
| (name2, uu____2801) -> begin
(extend_t env1 name2)
end)) env args)
in (

let uu____2802 = (

let uu____2803 = (

let uu____2815 = (FStar_List.map (fun uu____2831 -> (match (uu____2831) with
| (f, t) -> begin
(

let uu____2840 = (

let uu____2843 = (translate_type env1 t)
in ((uu____2843), (false)))
in ((f), (uu____2840)))
end)) fields)
in ((name1), ((FStar_List.length args)), (uu____2815)))
in DTypeFlat (uu____2803))
in FStar_Pervasives_Native.Some (uu____2802))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2858, name, _mangled_name, args, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2899 -> (match (uu____2899) with
| (name2, uu____2903) -> begin
(extend_t env1 name2)
end)) env args)
in (

let uu____2904 = (

let uu____2905 = (

let uu____2920 = (FStar_List.map (fun uu____2945 -> (match (uu____2945) with
| (cons1, ts) -> begin
(

let uu____2966 = (FStar_List.map (fun uu____2982 -> (match (uu____2982) with
| (name2, t) -> begin
(

let uu____2991 = (

let uu____2994 = (translate_type env1 t)
in ((uu____2994), (false)))
in ((name2), (uu____2991)))
end)) ts)
in ((cons1), (uu____2966)))
end)) branches)
in ((name1), ((FStar_List.length args)), (uu____2920)))
in DTypeVariant (uu____2905))
in FStar_Pervasives_Native.Some (uu____2904))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____3017, name, _mangled_name, uu____3020, uu____3021))::uu____3022) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
((FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations");
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____3044) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____3046) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Tuple ([]) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, uu____3056) -> begin
(

let uu____3057 = (find_t env name)
in TBound (uu____3057))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____3059, t2) -> begin
(

let uu____3061 = (

let uu____3064 = (translate_type env t1)
in (

let uu____3065 = (translate_type env t2)
in ((uu____3064), (uu____3065))))
in TArrow (uu____3061))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____3068 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3068 = "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____3071 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3071 = "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____3078 = (FStar_Util.must (mk_width m))
in TInt (uu____3078))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____3085 = (FStar_Util.must (mk_width m))
in TInt (uu____3085))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____3089 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3089 = "FStar.Buffer.buffer")) -> begin
(

let uu____3090 = (translate_type env arg)
in TBuf (uu____3090))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____3091)::[], p) when (

let uu____3094 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3094 = "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when (((ns = ("Prims")::[]) || (ns = ("FStar")::("Pervasives")::("Native")::[])) && (FStar_Util.starts_with t1 "tuple")) -> begin
(

let uu____3116 = (FStar_List.map (translate_type env) args)
in TTuple (uu____3116))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3128 = (

let uu____3135 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____3135)))
in TApp (uu____3128))
end
| uu____3138 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____3141 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____3141))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____3151 -> (match (uu____3151) with
| ((name, uu____3155), typ) -> begin
(

let uu____3159 = (translate_type env typ)
in {name = name; typ = uu____3159; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____3164) -> begin
(

let uu____3165 = (find env name)
in EBound (uu____3165))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____3169 = (

let uu____3172 = (FStar_Util.must (mk_op op))
in (

let uu____3173 = (FStar_Util.must (mk_width m))
in ((uu____3172), (uu____3173))))
in EOp (uu____3169))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____3176 = (

let uu____3179 = (FStar_Util.must (mk_bool_op op))
in ((uu____3179), (Bool)))
in EOp (uu____3176))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n1) -> begin
EQualified (n1)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3184); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print7})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun uu___125_3201 -> (match (uu___125_3201) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| uu____3202 -> begin
false
end)) flags)
in (

let uu____3203 = (match (is_mut) with
| true -> begin
(

let uu____3208 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when (

let uu____3212 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3212 = "FStar.ST.stackref")) -> begin
t
end
| uu____3213 -> begin
(

let uu____3214 = (

let uu____3215 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" uu____3215))
in (failwith uu____3214))
end)
in (

let uu____3217 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (uu____3218, (body1)::[]); FStar_Extraction_ML_Syntax.mlty = uu____3220; FStar_Extraction_ML_Syntax.loc = uu____3221} -> begin
body1
end
| uu____3223 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((uu____3208), (uu____3217))))
end
| uu____3224 -> begin
((typ), (body))
end)
in (match (uu____3203) with
| (typ1, body1) -> begin
(

let binder = (

let uu____3228 = (translate_type env typ1)
in {name = name; typ = uu____3228; mut = is_mut})
in (

let body2 = (translate_expr env body1)
in (

let env1 = (extend env name is_mut)
in (

let continuation1 = (translate_expr env1 continuation)
in ELet (((binder), (body2), (continuation1)))))))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(

let uu____3244 = (

let uu____3250 = (translate_expr env expr)
in (

let uu____3251 = (translate_branches env branches)
in ((uu____3250), (uu____3251))))
in EMatch (uu____3244))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3259; FStar_Extraction_ML_Syntax.loc = uu____3260}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v1, uu____3262); FStar_Extraction_ML_Syntax.mlty = uu____3263; FStar_Extraction_ML_Syntax.loc = uu____3264})::[]) when ((

let uu____3268 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3268 = "FStar.HyperStack.ST.op_Bang")) && (is_mutable env v1)) -> begin
(

let uu____3269 = (find env v1)
in EBound (uu____3269))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3271; FStar_Extraction_ML_Syntax.loc = uu____3272}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v1, uu____3274); FStar_Extraction_ML_Syntax.mlty = uu____3275; FStar_Extraction_ML_Syntax.loc = uu____3276})::(e1)::[]) when ((

let uu____3281 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3281 = "FStar.HyperStack.ST.op_Colon_Equals")) && (is_mutable env v1)) -> begin
(

let uu____3282 = (

let uu____3285 = (

let uu____3286 = (find env v1)
in EBound (uu____3286))
in (

let uu____3287 = (translate_expr env e1)
in ((uu____3285), (uu____3287))))
in EAssign (uu____3282))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3289; FStar_Extraction_ML_Syntax.loc = uu____3290}, (e1)::(e2)::[]) when ((

let uu____3296 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3296 = "FStar.Buffer.index")) || (

let uu____3298 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3298 = "FStar.Buffer.op_Array_Access"))) -> begin
(

let uu____3299 = (

let uu____3302 = (translate_expr env e1)
in (

let uu____3303 = (translate_expr env e2)
in ((uu____3302), (uu____3303))))
in EBufRead (uu____3299))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3305; FStar_Extraction_ML_Syntax.loc = uu____3306}, (e1)::(e2)::[]) when (

let uu____3310 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3310 = "FStar.Buffer.create")) -> begin
(

let uu____3311 = (

let uu____3315 = (translate_expr env e1)
in (

let uu____3316 = (translate_expr env e2)
in ((Stack), (uu____3315), (uu____3316))))
in EBufCreate (uu____3311))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3318; FStar_Extraction_ML_Syntax.loc = uu____3319}, (_e0)::(e1)::(e2)::[]) when (

let uu____3324 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3324 = "FStar.Buffer.rcreate")) -> begin
(

let uu____3325 = (

let uu____3329 = (translate_expr env e1)
in (

let uu____3330 = (translate_expr env e2)
in ((Eternal), (uu____3329), (uu____3330))))
in EBufCreate (uu____3325))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3332; FStar_Extraction_ML_Syntax.loc = uu____3333}, (e2)::[]) when (

let uu____3336 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3336 = "FStar.Buffer.createL")) -> begin
(

let rec list_elements1 = (fun acc e21 -> (match (e21.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd1)::(tl1)::[]) -> begin
(list_elements1 ((hd1)::acc) tl1)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| uu____3360 -> begin
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements2 = (list_elements1 [])
in (

let uu____3366 = (

let uu____3370 = (

let uu____3372 = (list_elements2 e2)
in (FStar_List.map (translate_expr env) uu____3372))
in ((Stack), (uu____3370)))
in EBufCreateL (uu____3366))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3376; FStar_Extraction_ML_Syntax.loc = uu____3377}, (e1)::(e2)::(_e3)::[]) when (

let uu____3382 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3382 = "FStar.Buffer.sub")) -> begin
(

let uu____3383 = (

let uu____3386 = (translate_expr env e1)
in (

let uu____3387 = (translate_expr env e2)
in ((uu____3386), (uu____3387))))
in EBufSub (uu____3383))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3389; FStar_Extraction_ML_Syntax.loc = uu____3390}, (e1)::(e2)::[]) when (

let uu____3394 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3394 = "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3396; FStar_Extraction_ML_Syntax.loc = uu____3397}, (e1)::(e2)::[]) when (

let uu____3401 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3401 = "FStar.Buffer.offset")) -> begin
(

let uu____3402 = (

let uu____3405 = (translate_expr env e1)
in (

let uu____3406 = (translate_expr env e2)
in ((uu____3405), (uu____3406))))
in EBufSub (uu____3402))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3408; FStar_Extraction_ML_Syntax.loc = uu____3409}, (e1)::(e2)::(e3)::[]) when ((

let uu____3416 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3416 = "FStar.Buffer.upd")) || (

let uu____3418 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3418 = "FStar.Buffer.op_Array_Assignment"))) -> begin
(

let uu____3419 = (

let uu____3423 = (translate_expr env e1)
in (

let uu____3424 = (translate_expr env e2)
in (

let uu____3425 = (translate_expr env e3)
in ((uu____3423), (uu____3424), (uu____3425)))))
in EBufWrite (uu____3419))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3427; FStar_Extraction_ML_Syntax.loc = uu____3428}, (uu____3429)::[]) when (

let uu____3431 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3431 = "FStar.HyperStack.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3433; FStar_Extraction_ML_Syntax.loc = uu____3434}, (uu____3435)::[]) when (

let uu____3437 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3437 = "FStar.HyperStack.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3439; FStar_Extraction_ML_Syntax.loc = uu____3440}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (

let uu____3447 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3447 = "FStar.Buffer.blit")) -> begin
(

let uu____3448 = (

let uu____3454 = (translate_expr env e1)
in (

let uu____3455 = (translate_expr env e2)
in (

let uu____3456 = (translate_expr env e3)
in (

let uu____3457 = (translate_expr env e4)
in (

let uu____3458 = (translate_expr env e5)
in ((uu____3454), (uu____3455), (uu____3456), (uu____3457), (uu____3458)))))))
in EBufBlit (uu____3448))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3460; FStar_Extraction_ML_Syntax.loc = uu____3461}, (e1)::(e2)::(e3)::[]) when (

let uu____3466 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3466 = "FStar.Buffer.fill")) -> begin
(

let uu____3467 = (

let uu____3471 = (translate_expr env e1)
in (

let uu____3472 = (translate_expr env e2)
in (

let uu____3473 = (translate_expr env e3)
in ((uu____3471), (uu____3472), (uu____3473)))))
in EBufFill (uu____3467))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3475; FStar_Extraction_ML_Syntax.loc = uu____3476}, (uu____3477)::[]) when (

let uu____3479 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3479 = "FStar.HyperStack.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3481; FStar_Extraction_ML_Syntax.loc = uu____3482}, (e1)::[]) when (

let uu____3485 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3485 = "Obj.repr")) -> begin
(

let uu____3486 = (

let uu____3489 = (translate_expr env e1)
in ((uu____3489), (TAny)))
in ECast (uu____3486))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____3492; FStar_Extraction_ML_Syntax.loc = uu____3493}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____3498 = (FStar_Util.must (mk_width m))
in (

let uu____3499 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____3498 uu____3499 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____3501; FStar_Extraction_ML_Syntax.loc = uu____3502}, args) when (is_bool_op op) -> begin
(

let uu____3507 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____3507 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____3509; FStar_Extraction_ML_Syntax.loc = uu____3510}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____3512; FStar_Extraction_ML_Syntax.loc = uu____3513})::[]) when (is_machine_int m) -> begin
(

let uu____3521 = (

let uu____3524 = (FStar_Util.must (mk_width m))
in ((uu____3524), (c)))
in EConstant (uu____3521))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____3526; FStar_Extraction_ML_Syntax.loc = uu____3527}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____3529; FStar_Extraction_ML_Syntax.loc = uu____3530})::[]) when (is_machine_int m) -> begin
(

let uu____3538 = (

let uu____3541 = (FStar_Util.must (mk_width m))
in ((uu____3541), (c)))
in EConstant (uu____3538))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____3542; FStar_Extraction_ML_Syntax.loc = uu____3543}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____3545; FStar_Extraction_ML_Syntax.loc = uu____3546})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____3550 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____3552; FStar_Extraction_ML_Syntax.loc = uu____3553}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____3558 = (

let uu____3561 = (translate_expr env arg)
in ((uu____3561), (TInt (UInt64))))
in ECast (uu____3558))
end
| uu____3562 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____3563 = (

let uu____3566 = (translate_expr env arg)
in ((uu____3566), (TInt (UInt32))))
in ECast (uu____3563))
end
| uu____3567 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____3568 = (

let uu____3571 = (translate_expr env arg)
in ((uu____3571), (TInt (UInt16))))
in ECast (uu____3568))
end
| uu____3572 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____3573 = (

let uu____3576 = (translate_expr env arg)
in ((uu____3576), (TInt (UInt8))))
in ECast (uu____3573))
end
| uu____3577 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____3578 = (

let uu____3581 = (translate_expr env arg)
in ((uu____3581), (TInt (Int64))))
in ECast (uu____3578))
end
| uu____3582 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____3583 = (

let uu____3586 = (translate_expr env arg)
in ((uu____3586), (TInt (Int32))))
in ECast (uu____3583))
end
| uu____3587 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____3588 = (

let uu____3591 = (translate_expr env arg)
in ((uu____3591), (TInt (Int16))))
in ECast (uu____3588))
end
| uu____3592 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____3593 = (

let uu____3596 = (translate_expr env arg)
in ((uu____3596), (TInt (Int8))))
in ECast (uu____3593))
end
| uu____3597 -> begin
(

let uu____3598 = (

let uu____3602 = (

let uu____3604 = (translate_expr env arg)
in (uu____3604)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____3602)))
in EApp (uu____3598))
end)
end)
end)
end)
end)
end)
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = uu____3609; FStar_Extraction_ML_Syntax.loc = uu____3610}, args) -> begin
(

let uu____3616 = (

let uu____3620 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (uu____3620)))
in EApp (uu____3616))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (name, uu____3625); FStar_Extraction_ML_Syntax.mlty = uu____3626; FStar_Extraction_ML_Syntax.loc = uu____3627}, args) -> begin
(

let uu____3631 = (

let uu____3635 = (

let uu____3636 = (find env name)
in EBound (uu____3636))
in (

let uu____3637 = (FStar_List.map (translate_expr env) args)
in ((uu____3635), (uu____3637))))
in EApp (uu____3631))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) -> begin
(

let uu____3643 = (

let uu____3646 = (translate_expr env e1)
in (

let uu____3647 = (translate_type env t_to)
in ((uu____3646), (uu____3647))))
in ECast (uu____3643))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____3648, fields) -> begin
(

let uu____3658 = (

let uu____3664 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3665 = (FStar_List.map (fun uu____3677 -> (match (uu____3677) with
| (field, expr) -> begin
(

let uu____3684 = (translate_expr env expr)
in ((field), (uu____3684)))
end)) fields)
in ((uu____3664), (uu____3665))))
in EFlat (uu____3658))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) -> begin
(

let uu____3690 = (

let uu____3694 = (assert_lid env e1.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3695 = (translate_expr env e1)
in ((uu____3694), (uu____3695), ((FStar_Pervasives_Native.snd path)))))
in EField (uu____3690))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____3697) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, uu____3705) -> begin
(

let uu____3708 = (

let uu____3709 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head1)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____3709))
in (failwith uu____3708))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____3713 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____3713))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____3717 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____3717))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3719, cons1), es) -> begin
(

let uu____3729 = (

let uu____3734 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3735 = (FStar_List.map (translate_expr env) es)
in ((uu____3734), (cons1), (uu____3735))))
in ECons (uu____3729))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env1 = (add_binders env args)
in (

let uu____3749 = (

let uu____3753 = (translate_expr env1 body)
in ((binders), (uu____3753)))
in EFun (uu____3749))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____3760 = (

let uu____3764 = (translate_expr env e1)
in (

let uu____3765 = (translate_expr env e2)
in (

let uu____3766 = (match (e3) with
| FStar_Pervasives_Native.None -> begin
EUnit
end
| FStar_Pervasives_Native.Some (e31) -> begin
(translate_expr env e31)
end)
in ((uu____3764), (uu____3765), (uu____3766)))))
in EIfThenElse (uu____3760))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____3768) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____3772) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____3780) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3796 = (

let uu____3803 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____3803)))
in TApp (uu____3796))
end
| uu____3806 -> begin
TQualified (lid)
end)
end
| uu____3807 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____3822 -> (match (uu____3822) with
| (pat, guard, expr) -> begin
(match ((guard = FStar_Pervasives_Native.None)) with
| true -> begin
(

let uu____3837 = (translate_pat env pat)
in (match (uu____3837) with
| (env1, pat1) -> begin
(

let uu____3844 = (translate_expr env1 expr)
in ((pat1), (uu____3844)))
end))
end
| uu____3845 -> begin
(failwith "todo: translate_branch")
end)
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  (env * pattern) = (fun env p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
((env), (PUnit))
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (b)) -> begin
((env), (PBool (b)))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____3854) -> begin
(

let env1 = (extend env name false)
in ((env1), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env1 = (extend env "_" false)
in ((env1), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3857, cons1), ps) -> begin
(

let uu____3867 = (FStar_List.fold_left (fun uu____3881 p1 -> (match (uu____3881) with
| (env1, acc) -> begin
(

let uu____3893 = (translate_pat env1 p1)
in (match (uu____3893) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3867) with
| (env1, ps1) -> begin
((env1), (PCons (((cons1), ((FStar_List.rev ps1))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____3910, ps) -> begin
(

let uu____3920 = (FStar_List.fold_left (fun uu____3942 uu____3943 -> (match (((uu____3942), (uu____3943))) with
| ((env1, acc), (field, p1)) -> begin
(

let uu____3980 = (translate_pat env1 p1)
in (match (uu____3980) with
| (env2, p2) -> begin
((env2), ((((field), (p2)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3920) with
| (env1, ps1) -> begin
((env1), (PRecord ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____4014 = (FStar_List.fold_left (fun uu____4028 p1 -> (match (uu____4028) with
| (env1, acc) -> begin
(

let uu____4040 = (translate_pat env1 p1)
in (match (uu____4040) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____4014) with
| (env1, ps1) -> begin
((env1), (PTuple ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____4056) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____4059) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____4066)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____4074) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____4075) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (uu____4076) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____4077) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (uu____4079, FStar_Pervasives_Native.None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____4090 = (

let uu____4094 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____4094)))
in EApp (uu____4090)))




