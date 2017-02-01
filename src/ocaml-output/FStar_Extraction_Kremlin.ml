
open Prims
type decl =
| DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) * typ * expr)
| DFunction of (cc Prims.option * flag Prims.list * typ * (Prims.string Prims.list * Prims.string) * binder Prims.list * expr)
| DTypeAlias of ((Prims.string Prims.list * Prims.string) * Prims.int * typ)
| DTypeFlat of ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list)
| DExternal of (cc Prims.option * (Prims.string Prims.list * Prims.string) * typ)
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
| uu____293 -> begin
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
| uu____341 -> begin
false
end))


let __proj__DFunction__item___0 : decl  ->  (cc Prims.option * flag Prims.list * typ * (Prims.string Prims.list * Prims.string) * binder Prims.list * expr) = (fun projectee -> (match (projectee) with
| DFunction (_0) -> begin
_0
end))


let uu___is_DTypeAlias : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeAlias (_0) -> begin
true
end
| uu____395 -> begin
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
| uu____436 -> begin
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
| uu____488 -> begin
false
end))


let __proj__DExternal__item___0 : decl  ->  (cc Prims.option * (Prims.string Prims.list * Prims.string) * typ) = (fun projectee -> (match (projectee) with
| DExternal (_0) -> begin
_0
end))


let uu___is_DTypeVariant : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeVariant (_0) -> begin
true
end
| uu____535 -> begin
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
| uu____588 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____592 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____596 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____600 -> begin
false
end))


let uu___is_NoExtract : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____604 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____608 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____612 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____616 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____620 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____625 -> begin
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
| uu____640 -> begin
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
| uu____663 -> begin
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
| uu____680 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____688 -> begin
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
| uu____712 -> begin
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
| uu____736 -> begin
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
| uu____758 -> begin
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
| uu____775 -> begin
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
| uu____796 -> begin
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
| uu____819 -> begin
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
| uu____840 -> begin
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
| uu____863 -> begin
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
| uu____886 -> begin
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
| uu____918 -> begin
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
| uu____947 -> begin
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
| uu____967 -> begin
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
| uu____984 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____988 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____993 -> begin
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
| uu____1004 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____1008 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____1013 -> begin
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
| uu____1030 -> begin
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
| uu____1060 -> begin
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
| uu____1083 -> begin
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
| uu____1104 -> begin
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
| uu____1126 -> begin
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
| uu____1145 -> begin
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
| uu____1172 -> begin
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
| uu____1193 -> begin
false
end))


let __proj__EString__item___0 : expr  ->  Prims.string = (fun projectee -> (match (projectee) with
| EString (_0) -> begin
_0
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____1204 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____1208 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____1212 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____1216 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____1220 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____1224 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____1228 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____1232 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____1236 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____1240 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____1244 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____1248 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____1252 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____1256 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____1260 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____1264 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____1268 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____1272 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____1276 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____1280 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____1284 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____1288 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____1292 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____1296 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____1300 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____1304 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____1309 -> begin
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
| uu____1321 -> begin
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
| uu____1336 -> begin
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
| uu____1358 -> begin
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
| uu____1376 -> begin
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
| uu____1396 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____1400 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____1404 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____1408 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____1412 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____1416 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____1420 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____1424 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____1428 -> begin
false
end))


let uu___is_Int : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int -> begin
true
end
| uu____1432 -> begin
false
end))


let uu___is_UInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt -> begin
true
end
| uu____1436 -> begin
false
end))


let uu___is_TInt : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TInt (_0) -> begin
true
end
| uu____1453 -> begin
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
| uu____1465 -> begin
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
| uu____1476 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____1484 -> begin
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
| uu____1504 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____1508 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____1515 -> begin
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
| uu____1532 -> begin
false
end))


let uu___is_TBound : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
true
end
| uu____1537 -> begin
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
| uu____1555 -> begin
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
| uu____1586 -> begin
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


let current_version : version = (Prims.parse_int "19")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun uu____1639 -> (match (uu____1639) with
| (x, uu____1644, uu____1645) -> begin
x
end))


let snd3 = (fun uu____1659 -> (match (uu____1659) with
| (uu____1663, x, uu____1665) -> begin
x
end))


let thd3 = (fun uu____1679 -> (match (uu____1679) with
| (uu____1683, uu____1684, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun uu___138_1689 -> (match (uu___138_1689) with
| "UInt8" -> begin
Some (UInt8)
end
| "UInt16" -> begin
Some (UInt16)
end
| "UInt32" -> begin
Some (UInt32)
end
| "UInt64" -> begin
Some (UInt64)
end
| "Int8" -> begin
Some (Int8)
end
| "Int16" -> begin
Some (Int16)
end
| "Int32" -> begin
Some (Int32)
end
| "Int64" -> begin
Some (Int64)
end
| uu____1691 -> begin
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun uu___139_1695 -> (match (uu___139_1695) with
| "op_Negation" -> begin
Some (Not)
end
| "op_AmpAmp" -> begin
Some (And)
end
| "op_BarBar" -> begin
Some (Or)
end
| "op_Equality" -> begin
Some (Eq)
end
| "op_disEquality" -> begin
Some (Neq)
end
| uu____1697 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun uu___140_1705 -> (match (uu___140_1705) with
| ("add") | ("op_Plus_Hat") -> begin
Some (Add)
end
| ("add_mod") | ("op_Plus_Percent_Hat") -> begin
Some (AddW)
end
| ("sub") | ("op_Subtraction_Hat") -> begin
Some (Sub)
end
| ("sub_mod") | ("op_Subtraction_Percent_Hat") -> begin
Some (SubW)
end
| ("mul") | ("op_Star_Hat") -> begin
Some (Mult)
end
| ("mul_mod") | ("op_Star_Percent_Hat") -> begin
Some (MultW)
end
| ("div") | ("op_Slash_Hat") -> begin
Some (Div)
end
| ("div_mod") | ("op_Slash_Percent_Hat") -> begin
Some (DivW)
end
| ("rem") | ("op_Percent_Hat") -> begin
Some (Mod)
end
| ("logor") | ("op_Bar_Hat") -> begin
Some (BOr)
end
| ("logxor") | ("op_Hat_Hat") -> begin
Some (BXor)
end
| ("logand") | ("op_Amp_Hat") -> begin
Some (BAnd)
end
| "lognot" -> begin
Some (BNot)
end
| ("shift_right") | ("op_Greater_Greater_Hat") -> begin
Some (BShiftR)
end
| ("shift_left") | ("op_Less_Less_Hat") -> begin
Some (BShiftL)
end
| ("eq") | ("op_Equals_Hat") -> begin
Some (Eq)
end
| ("op_Greater_Hat") | ("gt") -> begin
Some (Gt)
end
| ("op_Greater_Equals_Hat") | ("gte") -> begin
Some (Gte)
end
| ("op_Less_Hat") | ("lt") -> begin
Some (Lt)
end
| ("op_Less_Equals_Hat") | ("lte") -> begin
Some (Lte)
end
| uu____1707 -> begin
None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))

type env =
{names : name Prims.list; names_t : Prims.string Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; names_t = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let uu___145_1774 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = uu___145_1774.names_t; module_name = uu___145_1774.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___146_1781 = env
in {names = uu___146_1781.names; names_t = (x)::env.names_t; module_name = uu___146_1781.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____1788 = (FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)
in (match (uu____1788) with
| Some (name) -> begin
name
end
| None -> begin
(failwith "internal error: name not found")
end)))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (

let uu____1798 = (find_name env x)
in uu____1798.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| uu____1808 -> begin
(

let uu____1809 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____1809))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| uu____1819 -> begin
(

let uu____1820 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____1820))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env uu____1850 -> (match (uu____1850) with
| ((name, uu____1856), uu____1857) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____1948 -> (match (uu____1948) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____1979 = m
in (match (uu____1979) with
| ((prefix, final), uu____1991, uu____1992) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
(

let uu____2008 = (translate_module m)
in Some (uu____2008));
)
end)
with
| e -> begin
((

let uu____2013 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____2013));
None;
)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____2014 -> (match (uu____2014) with
| (module_name, modul, uu____2026) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| uu____2050 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun uu___141_2058 -> (match (uu___141_2058) with
| FStar_Extraction_ML_Syntax.Private -> begin
Some (Private)
end
| FStar_Extraction_ML_Syntax.NoExtract -> begin
Some (NoExtract)
end
| FStar_Extraction_ML_Syntax.Attribute ("c_inline") -> begin
Some (CInline)
end
| FStar_Extraction_ML_Syntax.Attribute ("substitute") -> begin
Some (Substitute)
end
| FStar_Extraction_ML_Syntax.Attribute (a) -> begin
((FStar_Util.print1_warning "Warning: unrecognized attribute %s" a);
None;
)
end
| uu____2062 -> begin
None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___142_2110 -> (match (uu___142_2110) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____2111 -> begin
false
end)) flags)
in (

let env = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____2113 -> begin
env
end)
in (

let rec find_return_type = (fun uu___143_2117 -> (match (uu___143_2117) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2118, uu____2119, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (

let uu____2123 = (find_return_type t0)
in (translate_type env uu____2123))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in (

let flags = (translate_flags flags)
in (match (assumed) with
| true -> begin
(

let uu____2135 = (

let uu____2136 = (

let uu____2144 = (translate_type env t0)
in ((None), (name), (uu____2144)))
in DExternal (uu____2136))
in Some (uu____2135))
end
| uu____2149 -> begin
try
(match (()) with
| () -> begin
(

let body = (translate_expr env body)
in Some (DFunction (((None), (flags), (t), (name), (binders), (body)))))
end)
with
| e -> begin
((

let uu____2164 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) uu____2164));
Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort))));
)
end
end)))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2175); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2177; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = uu____2179})::[]) -> begin
(

let flags = (translate_flags flags)
in (

let t = (translate_type env t)
in (

let name = ((env.module_name), (name))
in try
(match (()) with
| () -> begin
(

let expr = (translate_expr env expr)
in Some (DGlobal (((flags), (name), (t), (expr)))))
end)
with
| e -> begin
((

let uu____2205 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) uu____2205));
Some (DGlobal (((flags), (name), (t), (EAny))));
)
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2211, uu____2212, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2214); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2216; FStar_Extraction_ML_Syntax.mllb_def = uu____2217; FStar_Extraction_ML_Syntax.print_typ = uu____2218})::uu____2219) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
(match (ts) with
| Some (idents, t) -> begin
(

let uu____2229 = (

let uu____2230 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " uu____2230))
in (

let uu____2234 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" uu____2229 uu____2234)))
end
| None -> begin
()
end);
None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2236) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2238) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env uu____2270 -> (match (uu____2270) with
| (name, uu____2274) -> begin
(extend_t env name)
end)) env args)
in (match (assumed) with
| true -> begin
None
end
| uu____2276 -> begin
(

let uu____2277 = (

let uu____2278 = (

let uu____2285 = (translate_type env t)
in ((name), ((FStar_List.length args)), (uu____2285)))
in DTypeAlias (uu____2278))
in Some (uu____2277))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2291, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env uu____2325 -> (match (uu____2325) with
| (name, uu____2329) -> begin
(extend_t env name)
end)) env args)
in (

let uu____2330 = (

let uu____2331 = (

let uu____2343 = (FStar_List.map (fun uu____2355 -> (match (uu____2355) with
| (f, t) -> begin
(

let uu____2364 = (

let uu____2367 = (translate_type env t)
in ((uu____2367), (false)))
in ((f), (uu____2364)))
end)) fields)
in ((name), ((FStar_List.length args)), (uu____2343)))
in DTypeFlat (uu____2331))
in Some (uu____2330))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2380, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env uu____2415 -> (match (uu____2415) with
| (name, uu____2419) -> begin
(extend_t env name)
end)) env args)
in (

let uu____2420 = (

let uu____2421 = (

let uu____2436 = (FStar_List.mapi (fun i uu____2456 -> (match (uu____2456) with
| (cons, ts) -> begin
(

let uu____2471 = (FStar_List.mapi (fun j t -> (

let uu____2483 = (

let uu____2484 = (FStar_Util.string_of_int i)
in (

let uu____2485 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "x%s%s" uu____2484 uu____2485)))
in (

let uu____2486 = (

let uu____2489 = (translate_type env t)
in ((uu____2489), (false)))
in ((uu____2483), (uu____2486))))) ts)
in ((cons), (uu____2471)))
end)) branches)
in ((name), ((FStar_List.length args)), (uu____2436)))
in DTypeVariant (uu____2421))
in Some (uu____2420))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2510, name, _mangled_name, uu____2513, uu____2514))::uu____2515) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
((FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations");
None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____2537) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____2539) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, uu____2547) -> begin
(

let uu____2548 = (find_t env name)
in TBound (uu____2548))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____2550, t2) -> begin
(

let uu____2552 = (

let uu____2555 = (translate_type env t1)
in (

let uu____2556 = (translate_type env t2)
in ((uu____2555), (uu____2556))))
in TArrow (uu____2552))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____2567 = (FStar_Util.must (mk_width m))
in TInt (uu____2567))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____2574 = (FStar_Util.must (mk_width m))
in TInt (uu____2574))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(

let uu____2578 = (translate_type env arg)
in TBuf (uu____2578))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____2579)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (("Prims")::[], t)) when (FStar_Util.starts_with t "tuple") -> begin
(

let uu____2599 = (FStar_List.map (translate_type env) args)
in TTuple (uu____2599))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2608 = (

let uu____2615 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____2615)))
in TApp (uu____2608))
end
| uu____2618 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____2621 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____2621))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____2631 -> (match (uu____2631) with
| ((name, uu____2635), typ) -> begin
(

let uu____2639 = (translate_type env typ)
in {name = name; typ = uu____2639; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____2644) -> begin
(

let uu____2645 = (find env name)
in EBound (uu____2645))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____2649 = (

let uu____2652 = (FStar_Util.must (mk_op op))
in (

let uu____2653 = (FStar_Util.must (mk_width m))
in ((uu____2652), (uu____2653))))
in EOp (uu____2649))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____2656 = (

let uu____2659 = (FStar_Util.must (mk_bool_op op))
in ((uu____2659), (Bool)))
in EOp (uu____2656))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2664); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun uu___144_2680 -> (match (uu___144_2680) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| uu____2681 -> begin
false
end)) flags)
in (

let uu____2682 = (match (is_mut) with
| true -> begin
(

let uu____2687 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.stackref") -> begin
t
end
| uu____2691 -> begin
(

let uu____2692 = (

let uu____2693 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" uu____2693))
in (failwith uu____2692))
end)
in (

let uu____2695 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (uu____2696, (body)::[]); FStar_Extraction_ML_Syntax.mlty = uu____2698; FStar_Extraction_ML_Syntax.loc = uu____2699} -> begin
body
end
| uu____2701 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((uu____2687), (uu____2695))))
end
| uu____2702 -> begin
((typ), (body))
end)
in (match (uu____2682) with
| (typ, body) -> begin
(

let binder = (

let uu____2706 = (translate_type env typ)
in {name = name; typ = uu____2706; mut = is_mut})
in (

let body = (translate_expr env body)
in (

let env = (extend env name is_mut)
in (

let continuation = (translate_expr env continuation)
in ELet (((binder), (body), (continuation)))))))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(

let uu____2722 = (

let uu____2728 = (translate_expr env expr)
in (

let uu____2729 = (translate_branches env branches)
in ((uu____2728), (uu____2729))))
in EMatch (uu____2722))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2737; FStar_Extraction_ML_Syntax.loc = uu____2738}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, uu____2740); FStar_Extraction_ML_Syntax.mlty = uu____2741; FStar_Extraction_ML_Syntax.loc = uu____2742})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") && (is_mutable env v)) -> begin
(

let uu____2744 = (find env v)
in EBound (uu____2744))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2746; FStar_Extraction_ML_Syntax.loc = uu____2747}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, uu____2749); FStar_Extraction_ML_Syntax.mlty = uu____2750; FStar_Extraction_ML_Syntax.loc = uu____2751})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") && (is_mutable env v)) -> begin
(

let uu____2754 = (

let uu____2757 = (

let uu____2758 = (find env v)
in EBound (uu____2758))
in (

let uu____2759 = (translate_expr env e)
in ((uu____2757), (uu____2759))))
in EAssign (uu____2754))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2761; FStar_Extraction_ML_Syntax.loc = uu____2762}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(

let uu____2766 = (

let uu____2769 = (translate_expr env e1)
in (

let uu____2770 = (translate_expr env e2)
in ((uu____2769), (uu____2770))))
in EBufRead (uu____2766))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2772; FStar_Extraction_ML_Syntax.loc = uu____2773}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(

let uu____2777 = (

let uu____2781 = (translate_expr env e1)
in (

let uu____2782 = (translate_expr env e2)
in ((Stack), (uu____2781), (uu____2782))))
in EBufCreate (uu____2777))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2784; FStar_Extraction_ML_Syntax.loc = uu____2785}, (_e0)::(e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.rcreate") -> begin
(

let uu____2790 = (

let uu____2794 = (translate_expr env e1)
in (

let uu____2795 = (translate_expr env e2)
in ((Eternal), (uu____2794), (uu____2795))))
in EBufCreate (uu____2790))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2797; FStar_Extraction_ML_Syntax.loc = uu____2798}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| uu____2824 -> begin
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (

let uu____2830 = (

let uu____2834 = (

let uu____2836 = (list_elements e2)
in (FStar_List.map (translate_expr env) uu____2836))
in ((Stack), (uu____2834)))
in EBufCreateL (uu____2830))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2840; FStar_Extraction_ML_Syntax.loc = uu____2841}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(

let uu____2846 = (

let uu____2849 = (translate_expr env e1)
in (

let uu____2850 = (translate_expr env e2)
in ((uu____2849), (uu____2850))))
in EBufSub (uu____2846))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2852; FStar_Extraction_ML_Syntax.loc = uu____2853}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.join") -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2858; FStar_Extraction_ML_Syntax.loc = uu____2859}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(

let uu____2863 = (

let uu____2866 = (translate_expr env e1)
in (

let uu____2867 = (translate_expr env e2)
in ((uu____2866), (uu____2867))))
in EBufSub (uu____2863))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2869; FStar_Extraction_ML_Syntax.loc = uu____2870}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(

let uu____2875 = (

let uu____2879 = (translate_expr env e1)
in (

let uu____2880 = (translate_expr env e2)
in (

let uu____2881 = (translate_expr env e3)
in ((uu____2879), (uu____2880), (uu____2881)))))
in EBufWrite (uu____2875))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2883; FStar_Extraction_ML_Syntax.loc = uu____2884}, (uu____2885)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2888; FStar_Extraction_ML_Syntax.loc = uu____2889}, (uu____2890)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2893; FStar_Extraction_ML_Syntax.loc = uu____2894}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(

let uu____2901 = (

let uu____2907 = (translate_expr env e1)
in (

let uu____2908 = (translate_expr env e2)
in (

let uu____2909 = (translate_expr env e3)
in (

let uu____2910 = (translate_expr env e4)
in (

let uu____2911 = (translate_expr env e5)
in ((uu____2907), (uu____2908), (uu____2909), (uu____2910), (uu____2911)))))))
in EBufBlit (uu____2901))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2913; FStar_Extraction_ML_Syntax.loc = uu____2914}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.fill") -> begin
(

let uu____2919 = (

let uu____2923 = (translate_expr env e1)
in (

let uu____2924 = (translate_expr env e2)
in (

let uu____2925 = (translate_expr env e3)
in ((uu____2923), (uu____2924), (uu____2925)))))
in EBufFill (uu____2919))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2927; FStar_Extraction_ML_Syntax.loc = uu____2928}, (uu____2929)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.get") -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2932; FStar_Extraction_ML_Syntax.loc = uu____2933}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
(

let uu____2936 = (

let uu____2939 = (translate_expr env e)
in ((uu____2939), (TAny)))
in ECast (uu____2936))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____2942; FStar_Extraction_ML_Syntax.loc = uu____2943}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____2948 = (FStar_Util.must (mk_width m))
in (

let uu____2949 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____2948 uu____2949 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____2951; FStar_Extraction_ML_Syntax.loc = uu____2952}, args) when (is_bool_op op) -> begin
(

let uu____2957 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____2957 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(

let uu____2982 = (

let uu____2985 = (FStar_Util.must (mk_width m))
in ((uu____2985), (c)))
in EConstant (uu____2982))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____2986; FStar_Extraction_ML_Syntax.loc = uu____2987}, ({FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.mlty = uu____2989; FStar_Extraction_ML_Syntax.loc = uu____2990})::[]) -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____2994 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____2996; FStar_Extraction_ML_Syntax.loc = uu____2997}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____3002 = (

let uu____3005 = (translate_expr env arg)
in ((uu____3005), (TInt (UInt64))))
in ECast (uu____3002))
end
| uu____3006 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____3007 = (

let uu____3010 = (translate_expr env arg)
in ((uu____3010), (TInt (UInt32))))
in ECast (uu____3007))
end
| uu____3011 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____3012 = (

let uu____3015 = (translate_expr env arg)
in ((uu____3015), (TInt (UInt16))))
in ECast (uu____3012))
end
| uu____3016 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____3017 = (

let uu____3020 = (translate_expr env arg)
in ((uu____3020), (TInt (UInt8))))
in ECast (uu____3017))
end
| uu____3021 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____3022 = (

let uu____3025 = (translate_expr env arg)
in ((uu____3025), (TInt (Int64))))
in ECast (uu____3022))
end
| uu____3026 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____3027 = (

let uu____3030 = (translate_expr env arg)
in ((uu____3030), (TInt (Int32))))
in ECast (uu____3027))
end
| uu____3031 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____3032 = (

let uu____3035 = (translate_expr env arg)
in ((uu____3035), (TInt (Int16))))
in ECast (uu____3032))
end
| uu____3036 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____3037 = (

let uu____3040 = (translate_expr env arg)
in ((uu____3040), (TInt (Int8))))
in ECast (uu____3037))
end
| uu____3041 -> begin
(

let uu____3042 = (

let uu____3046 = (

let uu____3048 = (translate_expr env arg)
in (uu____3048)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____3046)))
in EApp (uu____3042))
end)
end)
end)
end)
end)
end)
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = uu____3053; FStar_Extraction_ML_Syntax.loc = uu____3054}, args) -> begin
(

let uu____3060 = (

let uu____3064 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (uu____3064)))
in EApp (uu____3060))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(

let uu____3071 = (

let uu____3074 = (translate_expr env e)
in (

let uu____3075 = (translate_type env t_to)
in ((uu____3074), (uu____3075))))
in ECast (uu____3071))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____3076, fields) -> begin
(

let uu____3086 = (

let uu____3092 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3093 = (FStar_List.map (fun uu____3101 -> (match (uu____3101) with
| (field, expr) -> begin
(

let uu____3108 = (translate_expr env expr)
in ((field), (uu____3108)))
end)) fields)
in ((uu____3092), (uu____3093))))
in EFlat (uu____3086))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(

let uu____3114 = (

let uu____3118 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3119 = (translate_expr env e)
in ((uu____3118), (uu____3119), ((Prims.snd path)))))
in EField (uu____3114))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____3121) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, uu____3129) -> begin
(

let uu____3132 = (

let uu____3133 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____3133))
in (failwith uu____3132))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____3137 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____3137))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____3141 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____3141))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3143, cons), es) -> begin
(

let uu____3153 = (

let uu____3158 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3159 = (FStar_List.map (translate_expr env) es)
in ((uu____3158), (cons), (uu____3159))))
in ECons (uu____3153))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____3162) -> begin
(failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____3173 = (

let uu____3177 = (translate_expr env e1)
in (

let uu____3178 = (translate_expr env e2)
in (

let uu____3179 = (match (e3) with
| None -> begin
EUnit
end
| Some (e3) -> begin
(translate_expr env e3)
end)
in ((uu____3177), (uu____3178), (uu____3179)))))
in EIfThenElse (uu____3173))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____3181) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____3185) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____3193) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3206 = (

let uu____3213 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____3213)))
in TApp (uu____3206))
end
| uu____3216 -> begin
TQualified (lid)
end)
end
| uu____3217 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____3232 -> (match (uu____3232) with
| (pat, guard, expr) -> begin
(match ((guard = None)) with
| true -> begin
(

let uu____3247 = (translate_pat env pat)
in (match (uu____3247) with
| (env, pat) -> begin
(

let uu____3254 = (translate_expr env expr)
in ((pat), (uu____3254)))
end))
end
| uu____3255 -> begin
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____3264) -> begin
(

let env = (extend env name false)
in ((env), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env = (extend env "_" false)
in ((env), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3267, cons), ps) -> begin
(

let uu____3277 = (FStar_List.fold_left (fun uu____3284 p -> (match (uu____3284) with
| (env, acc) -> begin
(

let uu____3296 = (translate_pat env p)
in (match (uu____3296) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3277) with
| (env, ps) -> begin
((env), (PCons (((cons), ((FStar_List.rev ps))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____3313, ps) -> begin
(

let uu____3323 = (FStar_List.fold_left (fun uu____3336 uu____3337 -> (match (((uu____3336), (uu____3337))) with
| ((env, acc), (field, p)) -> begin
(

let uu____3374 = (translate_pat env p)
in (match (uu____3374) with
| (env, p) -> begin
((env), ((((field), (p)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3323) with
| (env, ps) -> begin
((env), (PRecord ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____3408 = (FStar_List.fold_left (fun uu____3415 p -> (match (uu____3415) with
| (env, acc) -> begin
(

let uu____3427 = (translate_pat env p)
in (match (uu____3427) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3408) with
| (env, ps) -> begin
((env), (PTuple ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____3443) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____3446) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (uu____3453)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____3461) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____3462) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (uu____3463) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____3464) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (uu____3466, None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____3477 = (

let uu____3481 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____3481)))
in EApp (uu____3477)))




