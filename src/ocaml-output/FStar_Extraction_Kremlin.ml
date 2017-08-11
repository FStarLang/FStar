
open Prims
open FStar_Pervasives
type decl =
| DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) * typ * expr)
| DFunction of (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ * (Prims.string Prims.list * Prims.string) * binder Prims.list * expr)
| DTypeAlias of ((Prims.string Prims.list * Prims.string) * Prims.int * typ)
| DTypeFlat of ((Prims.string Prims.list * Prims.string) * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list)
| DExternal of (cc FStar_Pervasives_Native.option * (Prims.string Prims.list * Prims.string) * typ)
| DTypeVariant of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list) 
 and cc =
| StdCall
| CDecl
| FastCall 
 and flag =
| Private
| NoExtract
| CInline
| Substitute
| GCType 
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
| EFun of (binder Prims.list * expr * typ)
| EAbortS of Prims.string 
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
| uu____510 -> begin
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
| uu____598 -> begin
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
| uu____702 -> begin
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
| uu____774 -> begin
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
| uu____868 -> begin
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
| uu____956 -> begin
false
end))


let __proj__DTypeVariant__item___0 : decl  ->  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list) = (fun projectee -> (match (projectee) with
| DTypeVariant (_0) -> begin
_0
end))


let uu___is_StdCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| StdCall -> begin
true
end
| uu____1065 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____1070 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____1075 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1080 -> begin
false
end))


let uu___is_NoExtract : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____1085 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1090 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1095 -> begin
false
end))


let uu___is_GCType : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GCType -> begin
true
end
| uu____1100 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____1105 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____1110 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____1116 -> begin
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
| uu____1136 -> begin
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
| uu____1172 -> begin
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
| uu____1197 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____1209 -> begin
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
| uu____1247 -> begin
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
| uu____1285 -> begin
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
| uu____1319 -> begin
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
| uu____1343 -> begin
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
| uu____1375 -> begin
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
| uu____1411 -> begin
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
| uu____1443 -> begin
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
| uu____1479 -> begin
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
| uu____1515 -> begin
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
| uu____1569 -> begin
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
| uu____1617 -> begin
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
| uu____1647 -> begin
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
| uu____1672 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____1677 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____1683 -> begin
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
| uu____1696 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____1701 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____1707 -> begin
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
| uu____1731 -> begin
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
| uu____1781 -> begin
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
| uu____1817 -> begin
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
| uu____1849 -> begin
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
| uu____1883 -> begin
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
| uu____1911 -> begin
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
| uu____1955 -> begin
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
| uu____1987 -> begin
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
| uu____2009 -> begin
false
end))


let __proj__EFun__item___0 : expr  ->  (binder Prims.list * expr * typ) = (fun projectee -> (match (projectee) with
| EFun (_0) -> begin
_0
end))


let uu___is_EAbortS : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbortS (_0) -> begin
true
end
| uu____2047 -> begin
false
end))


let __proj__EAbortS__item___0 : expr  ->  Prims.string = (fun projectee -> (match (projectee) with
| EAbortS (_0) -> begin
_0
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____2060 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____2065 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____2070 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____2075 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____2080 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____2085 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____2090 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____2095 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____2100 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____2105 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____2110 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____2115 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____2120 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____2125 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____2130 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____2135 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____2140 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____2145 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____2150 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____2155 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____2160 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____2165 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____2170 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____2175 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____2180 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____2185 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____2191 -> begin
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
| uu____2205 -> begin
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
| uu____2225 -> begin
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
| uu____2259 -> begin
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
| uu____2285 -> begin
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
| uu____2316 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____2321 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____2326 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____2331 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____2336 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____2341 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____2346 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____2351 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____2356 -> begin
false
end))


let uu___is_Int : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int -> begin
true
end
| uu____2361 -> begin
false
end))


let uu___is_UInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt -> begin
true
end
| uu____2366 -> begin
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
| uu____2393 -> begin
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
| uu____2407 -> begin
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
| uu____2420 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____2432 -> begin
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
| uu____2463 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____2468 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____2478 -> begin
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
| uu____2503 -> begin
false
end))


let uu___is_TBound : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
true
end
| uu____2509 -> begin
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
| uu____2535 -> begin
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
| uu____2587 -> begin
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


let current_version : version = (Prims.parse_int "22")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 : 'Auu____2668 'Auu____2669 'Auu____2670 . ('Auu____2670 * 'Auu____2669 * 'Auu____2668)  ->  'Auu____2670 = (fun uu____2680 -> (match (uu____2680) with
| (x, uu____2688, uu____2689) -> begin
x
end))


let snd3 : 'Auu____2698 'Auu____2699 'Auu____2700 . ('Auu____2700 * 'Auu____2699 * 'Auu____2698)  ->  'Auu____2699 = (fun uu____2710 -> (match (uu____2710) with
| (uu____2717, x, uu____2719) -> begin
x
end))


let thd3 : 'Auu____2728 'Auu____2729 'Auu____2730 . ('Auu____2730 * 'Auu____2729 * 'Auu____2728)  ->  'Auu____2728 = (fun uu____2740 -> (match (uu____2740) with
| (uu____2747, uu____2748, x) -> begin
x
end))


let mk_width : Prims.string  ->  width FStar_Pervasives_Native.option = (fun uu___123_2755 -> (match (uu___123_2755) with
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
| uu____2758 -> begin
FStar_Pervasives_Native.None
end))


let mk_bool_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___124_2764 -> (match (uu___124_2764) with
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
| uu____2767 -> begin
FStar_Pervasives_Native.None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> FStar_Pervasives_Native.None))


let mk_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___125_2779 -> (match (uu___125_2779) with
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
| uu____2782 -> begin
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

let uu___130_2904 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = uu___130_2904.names_t; module_name = uu___130_2904.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___131_2913 = env
in {names = uu___131_2913.names; names_t = (x)::env.names_t; module_name = uu___131_2913.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____2922 = (FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)
in (match (uu____2922) with
| FStar_Pervasives_Native.Some (name) -> begin
name
end
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: name not found")
end)))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (

let uu____2936 = (find_name env x)
in uu____2936.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| uu____2953 -> begin
(

let uu____2954 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____2954))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| uu____2971 -> begin
(

let uu____2972 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____2972))
end)


let add_binders : 'Auu____2981 'Auu____2982 . env  ->  ((Prims.string * 'Auu____2982) * 'Auu____2981) Prims.list  ->  env = (fun env binders -> (FStar_List.fold_left (fun env1 uu____3025 -> (match (uu____3025) with
| ((name, uu____3035), uu____3036) -> begin
(extend env1 name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____3165 -> (match (uu____3165) with
| FStar_Extraction_ML_Syntax.MLLib (modules1) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____3225 = m
in (match (uu____3225) with
| ((prefix1, final), uu____3246, uu____3247) -> begin
(FStar_String.concat "." (FStar_List.append prefix1 ((final)::[])))
end))
in try
(match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
(

let uu____3279 = (translate_module m)
in FStar_Pervasives_Native.Some (uu____3279));
)
end)
with
| e -> begin
((

let uu____3288 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____3288));
FStar_Pervasives_Native.None;
)
end)) modules1)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____3289 -> (match (uu____3289) with
| (module_name, modul, uu____3310) -> begin
(

let module_name1 = (FStar_List.append (FStar_Pervasives_Native.fst module_name) (((FStar_Pervasives_Native.snd module_name))::[]))
in (

let program = (match (modul) with
| FStar_Pervasives_Native.Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name1)) decls)
end
| uu____3353 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name1)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.meta Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun uu___126_3368 -> (match (uu___126_3368) with
| FStar_Extraction_ML_Syntax.Private -> begin
FStar_Pervasives_Native.Some (Private)
end
| FStar_Extraction_ML_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (NoExtract)
end
| FStar_Extraction_ML_Syntax.CInline -> begin
FStar_Pervasives_Native.Some (CInline)
end
| FStar_Extraction_ML_Syntax.Substitute -> begin
FStar_Pervasives_Native.Some (Substitute)
end
| FStar_Extraction_ML_Syntax.GCType -> begin
FStar_Pervasives_Native.Some (GCType)
end
| uu____3371 -> begin
FStar_Pervasives_Native.None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl FStar_Pervasives_Native.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3379); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3382; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____3385; FStar_Extraction_ML_Syntax.loc = uu____3386}; FStar_Extraction_ML_Syntax.print_typ = uu____3387})::[]) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___127_3408 -> (match (uu___127_3408) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____3409 -> begin
false
end)) flags)
in (

let env1 = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____3411 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 uu____3422 -> (match (uu____3422) with
| (name1, uu____3428) -> begin
(extend_t env2 name1)
end)) env1 tvars)
in (

let rec find_return_type = (fun i uu___128_3435 -> (match (uu___128_3435) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3436, uu____3437, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type (i - (Prims.parse_int "1")) t)
end
| t -> begin
t
end))
in (

let t = (

let uu____3441 = (find_return_type (FStar_List.length args) t0)
in (translate_type env2 uu____3441))
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

let uu____3466 = (

let uu____3467 = (

let uu____3482 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (name1), (uu____3482)))
in DExternal (uu____3467))
in FStar_Pervasives_Native.Some (uu____3466))
end
| uu____3491 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____3492 -> begin
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

let uu____3521 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____3521));
FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (EAbort))));
)
end
end))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3539); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3542; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____3545; FStar_Extraction_ML_Syntax.loc = uu____3546}, uu____3547, uu____3548); FStar_Extraction_ML_Syntax.mlty = uu____3549; FStar_Extraction_ML_Syntax.loc = uu____3550}; FStar_Extraction_ML_Syntax.print_typ = uu____3551})::[]) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___127_3572 -> (match (uu___127_3572) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____3573 -> begin
false
end)) flags)
in (

let env1 = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____3575 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 uu____3586 -> (match (uu____3586) with
| (name1, uu____3592) -> begin
(extend_t env2 name1)
end)) env1 tvars)
in (

let rec find_return_type = (fun i uu___128_3599 -> (match (uu___128_3599) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3600, uu____3601, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type (i - (Prims.parse_int "1")) t)
end
| t -> begin
t
end))
in (

let t = (

let uu____3605 = (find_return_type (FStar_List.length args) t0)
in (translate_type env2 uu____3605))
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

let uu____3630 = (

let uu____3631 = (

let uu____3646 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (name1), (uu____3646)))
in DExternal (uu____3631))
in FStar_Pervasives_Native.Some (uu____3630))
end
| uu____3655 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____3656 -> begin
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

let uu____3685 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____3685));
FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (EAbort))));
)
end
end))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3703); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3705; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = uu____3707})::[]) -> begin
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

let uu____3755 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____3755));
FStar_Pervasives_Native.Some (DGlobal (((flags1), (name1), (t1), (EAny))));
)
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____3766, uu____3767, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3769); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3771; FStar_Extraction_ML_Syntax.mllb_def = uu____3772; FStar_Extraction_ML_Syntax.print_typ = uu____3773})::uu____3774) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
(match (ts) with
| FStar_Pervasives_Native.Some (idents, t) -> begin
(

let uu____3789 = (

let uu____3790 = (FStar_List.map FStar_Pervasives_Native.fst idents)
in (FStar_String.concat ", " uu____3790))
in (

let uu____3797 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" uu____3789 uu____3797)))
end
| FStar_Pervasives_Native.None -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____3800) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____3803) -> begin
FStar_Pervasives_Native.None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, uu____3808, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____3867 -> (match (uu____3867) with
| (name2, uu____3873) -> begin
(extend_t env1 name2)
end)) env args)
in (match (assumed) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3876 -> begin
(

let uu____3877 = (

let uu____3878 = (

let uu____3891 = (translate_type env1 t)
in ((name1), ((FStar_List.length args)), (uu____3891)))
in DTypeAlias (uu____3878))
in FStar_Pervasives_Native.Some (uu____3877))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____3898, name, _mangled_name, args, uu____3902, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____3967 -> (match (uu____3967) with
| (name2, uu____3973) -> begin
(extend_t env1 name2)
end)) env args)
in (

let uu____3974 = (

let uu____3975 = (

let uu____3998 = (FStar_List.map (fun uu____4025 -> (match (uu____4025) with
| (f, t) -> begin
(

let uu____4040 = (

let uu____4045 = (translate_type env1 t)
in ((uu____4045), (false)))
in ((f), (uu____4040)))
end)) fields)
in ((name1), ((FStar_List.length args)), (uu____3998)))
in DTypeFlat (uu____3975))
in FStar_Pervasives_Native.Some (uu____3974))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____4066, name, _mangled_name, args, attrs, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let flags = (translate_flags attrs)
in (

let env1 = (FStar_List.fold_left (fun env1 uu____4144 -> (match (uu____4144) with
| (name2, uu____4150) -> begin
(extend_t env1 name2)
end)) env args)
in (

let uu____4151 = (

let uu____4152 = (

let uu____4185 = (FStar_List.map (fun uu____4230 -> (match (uu____4230) with
| (cons1, ts) -> begin
(

let uu____4269 = (FStar_List.map (fun uu____4296 -> (match (uu____4296) with
| (name2, t) -> begin
(

let uu____4311 = (

let uu____4316 = (translate_type env1 t)
in ((uu____4316), (false)))
in ((name2), (uu____4311)))
end)) ts)
in ((cons1), (uu____4269)))
end)) branches)
in ((name1), (flags), ((FStar_List.length args)), (uu____4185)))
in DTypeVariant (uu____4152))
in FStar_Pervasives_Native.Some (uu____4151)))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____4355, name, _mangled_name, uu____4358, uu____4359, uu____4360))::uu____4361) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
((FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations");
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____4406) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____4409) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Tuple ([]) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, uu____4425) -> begin
(

let uu____4426 = (find_t env name)
in TBound (uu____4426))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____4428, t2) -> begin
(

let uu____4430 = (

let uu____4435 = (translate_type env t1)
in (

let uu____4436 = (translate_type env t2)
in ((uu____4435), (uu____4436))))
in TArrow (uu____4430))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____4440 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4440 = "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____4444 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4444 = "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____4456 = (FStar_Util.must (mk_width m))
in TInt (uu____4456))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____4468 = (FStar_Util.must (mk_width m))
in TInt (uu____4468))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____4473 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4473 = "FStar.Monotonic.HyperStack.mem")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____4478 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4478 = "FStar.Buffer.buffer")) -> begin
(

let uu____4479 = (translate_type env arg)
in TBuf (uu____4479))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____4480)::[], p) when (

let uu____4484 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4484 = "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when (((ns = ("Prims")::[]) || (ns = ("FStar")::("Pervasives")::("Native")::[])) && (FStar_Util.starts_with t1 "tuple")) -> begin
(

let uu____4522 = (FStar_List.map (translate_type env) args)
in TTuple (uu____4522))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4531 = (

let uu____4544 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____4544)))
in TApp (uu____4531))
end
| uu____4549 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____4553 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____4553))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____4569 -> (match (uu____4569) with
| ((name, uu____4575), typ) -> begin
(

let uu____4581 = (translate_type env typ)
in {name = name; typ = uu____4581; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____4586) -> begin
(

let uu____4587 = (find env name)
in EBound (uu____4587))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____4592 = (

let uu____4597 = (FStar_Util.must (mk_op op))
in (

let uu____4598 = (FStar_Util.must (mk_width m))
in ((uu____4597), (uu____4598))))
in EOp (uu____4592))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____4602 = (

let uu____4607 = (FStar_Util.must (mk_bool_op op))
in ((uu____4607), (Bool)))
in EOp (uu____4602))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n1) -> begin
EQualified (n1)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____4612); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print7})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun uu___129_4638 -> (match (uu___129_4638) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| uu____4639 -> begin
false
end)) flags)
in (

let uu____4640 = (match (is_mut) with
| true -> begin
(

let uu____4649 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when (

let uu____4654 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4654 = "FStar.ST.stackref")) -> begin
t
end
| uu____4655 -> begin
(

let uu____4656 = (

let uu____4657 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" uu____4657))
in (failwith uu____4656))
end)
in (

let uu____4660 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (uu____4661, (body1)::[]); FStar_Extraction_ML_Syntax.mlty = uu____4663; FStar_Extraction_ML_Syntax.loc = uu____4664} -> begin
body1
end
| uu____4667 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((uu____4649), (uu____4660))))
end
| uu____4668 -> begin
((typ), (body))
end)
in (match (uu____4640) with
| (typ1, body1) -> begin
(

let binder = (

let uu____4672 = (translate_type env typ1)
in {name = name; typ = uu____4672; mut = is_mut})
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

let uu____4698 = (

let uu____4709 = (translate_expr env expr)
in (

let uu____4710 = (translate_branches env branches)
in ((uu____4709), (uu____4710))))
in EMatch (uu____4698))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4724; FStar_Extraction_ML_Syntax.loc = uu____4725}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v1, uu____4727); FStar_Extraction_ML_Syntax.mlty = uu____4728; FStar_Extraction_ML_Syntax.loc = uu____4729})::[]) when ((

let uu____4734 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4734 = "FStar.HyperStack.ST.op_Bang")) && (is_mutable env v1)) -> begin
(

let uu____4735 = (find env v1)
in EBound (uu____4735))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4737; FStar_Extraction_ML_Syntax.loc = uu____4738}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v1, uu____4740); FStar_Extraction_ML_Syntax.mlty = uu____4741; FStar_Extraction_ML_Syntax.loc = uu____4742})::(e1)::[]) when ((

let uu____4748 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4748 = "FStar.HyperStack.ST.op_Colon_Equals")) && (is_mutable env v1)) -> begin
(

let uu____4749 = (

let uu____4754 = (

let uu____4755 = (find env v1)
in EBound (uu____4755))
in (

let uu____4756 = (translate_expr env e1)
in ((uu____4754), (uu____4756))))
in EAssign (uu____4749))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4758; FStar_Extraction_ML_Syntax.loc = uu____4759}, (e1)::(e2)::[]) when ((

let uu____4766 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4766 = "FStar.Buffer.index")) || (

let uu____4768 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4768 = "FStar.Buffer.op_Array_Access"))) -> begin
(

let uu____4769 = (

let uu____4774 = (translate_expr env e1)
in (

let uu____4775 = (translate_expr env e2)
in ((uu____4774), (uu____4775))))
in EBufRead (uu____4769))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4777; FStar_Extraction_ML_Syntax.loc = uu____4778}, (e1)::(e2)::[]) when (

let uu____4783 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4783 = "FStar.Buffer.create")) -> begin
(

let uu____4784 = (

let uu____4791 = (translate_expr env e1)
in (

let uu____4792 = (translate_expr env e2)
in ((Stack), (uu____4791), (uu____4792))))
in EBufCreate (uu____4784))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4794; FStar_Extraction_ML_Syntax.loc = uu____4795}, (_e0)::(e1)::(e2)::[]) when (

let uu____4801 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4801 = "FStar.Buffer.rcreate")) -> begin
(

let uu____4802 = (

let uu____4809 = (translate_expr env e1)
in (

let uu____4810 = (translate_expr env e2)
in ((Eternal), (uu____4809), (uu____4810))))
in EBufCreate (uu____4802))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4812; FStar_Extraction_ML_Syntax.loc = uu____4813}, (e2)::[]) when (

let uu____4817 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4817 = "FStar.Buffer.createL")) -> begin
(

let rec list_elements1 = (fun acc e21 -> (match (e21.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd1)::(tl1)::[]) -> begin
(list_elements1 ((hd1)::acc) tl1)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| uu____4855 -> begin
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements2 = (list_elements1 [])
in (

let uu____4863 = (

let uu____4870 = (

let uu____4873 = (list_elements2 e2)
in (FStar_List.map (translate_expr env) uu____4873))
in ((Stack), (uu____4870)))
in EBufCreateL (uu____4863))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4879; FStar_Extraction_ML_Syntax.loc = uu____4880}, (e1)::(e2)::(_e3)::[]) when (

let uu____4886 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4886 = "FStar.Buffer.sub")) -> begin
(

let uu____4887 = (

let uu____4892 = (translate_expr env e1)
in (

let uu____4893 = (translate_expr env e2)
in ((uu____4892), (uu____4893))))
in EBufSub (uu____4887))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4895; FStar_Extraction_ML_Syntax.loc = uu____4896}, (e1)::(e2)::[]) when (

let uu____4901 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4901 = "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4903; FStar_Extraction_ML_Syntax.loc = uu____4904}, (e1)::(e2)::[]) when (

let uu____4909 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4909 = "FStar.Buffer.offset")) -> begin
(

let uu____4910 = (

let uu____4915 = (translate_expr env e1)
in (

let uu____4916 = (translate_expr env e2)
in ((uu____4915), (uu____4916))))
in EBufSub (uu____4910))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4918; FStar_Extraction_ML_Syntax.loc = uu____4919}, (e1)::(e2)::(e3)::[]) when ((

let uu____4927 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4927 = "FStar.Buffer.upd")) || (

let uu____4929 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4929 = "FStar.Buffer.op_Array_Assignment"))) -> begin
(

let uu____4930 = (

let uu____4937 = (translate_expr env e1)
in (

let uu____4938 = (translate_expr env e2)
in (

let uu____4939 = (translate_expr env e3)
in ((uu____4937), (uu____4938), (uu____4939)))))
in EBufWrite (uu____4930))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4941; FStar_Extraction_ML_Syntax.loc = uu____4942}, (uu____4943)::[]) when (

let uu____4946 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4946 = "FStar.HyperStack.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4948; FStar_Extraction_ML_Syntax.loc = uu____4949}, (uu____4950)::[]) when (

let uu____4953 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4953 = "FStar.HyperStack.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4955; FStar_Extraction_ML_Syntax.loc = uu____4956}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (

let uu____4964 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4964 = "FStar.Buffer.blit")) -> begin
(

let uu____4965 = (

let uu____4976 = (translate_expr env e1)
in (

let uu____4977 = (translate_expr env e2)
in (

let uu____4978 = (translate_expr env e3)
in (

let uu____4979 = (translate_expr env e4)
in (

let uu____4980 = (translate_expr env e5)
in ((uu____4976), (uu____4977), (uu____4978), (uu____4979), (uu____4980)))))))
in EBufBlit (uu____4965))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4982; FStar_Extraction_ML_Syntax.loc = uu____4983}, (e1)::(e2)::(e3)::[]) when (

let uu____4989 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4989 = "FStar.Buffer.fill")) -> begin
(

let uu____4990 = (

let uu____4997 = (translate_expr env e1)
in (

let uu____4998 = (translate_expr env e2)
in (

let uu____4999 = (translate_expr env e3)
in ((uu____4997), (uu____4998), (uu____4999)))))
in EBufFill (uu____4990))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5001; FStar_Extraction_ML_Syntax.loc = uu____5002}, (uu____5003)::[]) when (

let uu____5006 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____5006 = "FStar.HyperStack.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5008; FStar_Extraction_ML_Syntax.loc = uu____5009}, (e1)::[]) when (

let uu____5013 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____5013 = "Obj.repr")) -> begin
(

let uu____5014 = (

let uu____5019 = (translate_expr env e1)
in ((uu____5019), (TAny)))
in ECast (uu____5014))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____5022; FStar_Extraction_ML_Syntax.loc = uu____5023}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____5031 = (FStar_Util.must (mk_width m))
in (

let uu____5032 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____5031 uu____5032 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____5034; FStar_Extraction_ML_Syntax.loc = uu____5035}, args) when (is_bool_op op) -> begin
(

let uu____5043 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____5043 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____5045; FStar_Extraction_ML_Syntax.loc = uu____5046}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____5048; FStar_Extraction_ML_Syntax.loc = uu____5049})::[]) when (is_machine_int m) -> begin
(

let uu____5064 = (

let uu____5069 = (FStar_Util.must (mk_width m))
in ((uu____5069), (c)))
in EConstant (uu____5064))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____5071; FStar_Extraction_ML_Syntax.loc = uu____5072}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____5074; FStar_Extraction_ML_Syntax.loc = uu____5075})::[]) when (is_machine_int m) -> begin
(

let uu____5090 = (

let uu____5095 = (FStar_Util.must (mk_width m))
in ((uu____5095), (c)))
in EConstant (uu____5090))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____5096; FStar_Extraction_ML_Syntax.loc = uu____5097}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____5099; FStar_Extraction_ML_Syntax.loc = uu____5100})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____5106 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____5108; FStar_Extraction_ML_Syntax.loc = uu____5109}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____5116 = (

let uu____5121 = (translate_expr env arg)
in ((uu____5121), (TInt (UInt64))))
in ECast (uu____5116))
end
| uu____5122 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____5123 = (

let uu____5128 = (translate_expr env arg)
in ((uu____5128), (TInt (UInt32))))
in ECast (uu____5123))
end
| uu____5129 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____5130 = (

let uu____5135 = (translate_expr env arg)
in ((uu____5135), (TInt (UInt16))))
in ECast (uu____5130))
end
| uu____5136 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____5137 = (

let uu____5142 = (translate_expr env arg)
in ((uu____5142), (TInt (UInt8))))
in ECast (uu____5137))
end
| uu____5143 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____5144 = (

let uu____5149 = (translate_expr env arg)
in ((uu____5149), (TInt (Int64))))
in ECast (uu____5144))
end
| uu____5150 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____5151 = (

let uu____5156 = (translate_expr env arg)
in ((uu____5156), (TInt (Int32))))
in ECast (uu____5151))
end
| uu____5157 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____5158 = (

let uu____5163 = (translate_expr env arg)
in ((uu____5163), (TInt (Int16))))
in ECast (uu____5158))
end
| uu____5164 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____5165 = (

let uu____5170 = (translate_expr env arg)
in ((uu____5170), (TInt (Int8))))
in ECast (uu____5165))
end
| uu____5171 -> begin
(

let uu____5172 = (

let uu____5179 = (

let uu____5182 = (translate_expr env arg)
in (uu____5182)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____5179)))
in EApp (uu____5172))
end)
end)
end)
end)
end)
end)
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = uu____5189; FStar_Extraction_ML_Syntax.loc = uu____5190}, args) -> begin
(

let uu____5200 = (

let uu____5207 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (uu____5207)))
in EApp (uu____5200))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (name, uu____5215); FStar_Extraction_ML_Syntax.mlty = uu____5216; FStar_Extraction_ML_Syntax.loc = uu____5217}, args) -> begin
(

let uu____5223 = (

let uu____5230 = (

let uu____5231 = (find env name)
in EBound (uu____5231))
in (

let uu____5232 = (FStar_List.map (translate_expr env) args)
in ((uu____5230), (uu____5232))))
in EApp (uu____5223))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) -> begin
(

let uu____5240 = (

let uu____5245 = (translate_expr env e1)
in (

let uu____5246 = (translate_type env t_to)
in ((uu____5245), (uu____5246))))
in ECast (uu____5240))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____5247, fields) -> begin
(

let uu____5265 = (

let uu____5276 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5277 = (FStar_List.map (fun uu____5296 -> (match (uu____5296) with
| (field, expr) -> begin
(

let uu____5307 = (translate_expr env expr)
in ((field), (uu____5307)))
end)) fields)
in ((uu____5276), (uu____5277))))
in EFlat (uu____5265))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) -> begin
(

let uu____5316 = (

let uu____5323 = (assert_lid env e1.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5324 = (translate_expr env e1)
in ((uu____5323), (uu____5324), ((FStar_Pervasives_Native.snd path)))))
in EField (uu____5316))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____5327) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, uu____5341) -> begin
(

let uu____5346 = (

let uu____5347 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head1)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____5347))
in (failwith uu____5346))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____5353 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____5353))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____5359 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____5359))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5362, cons1), es) -> begin
(

let uu____5379 = (

let uu____5388 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5389 = (FStar_List.map (translate_expr env) es)
in ((uu____5388), (cons1), (uu____5389))))
in ECons (uu____5379))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env1 = (add_binders env args)
in (

let uu____5412 = (

let uu____5421 = (translate_expr env1 body)
in (

let uu____5422 = (translate_type env1 body.FStar_Extraction_ML_Syntax.mlty)
in ((binders), (uu____5421), (uu____5422))))
in EFun (uu____5412))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____5432 = (

let uu____5439 = (translate_expr env e1)
in (

let uu____5440 = (translate_expr env e2)
in (

let uu____5441 = (match (e3) with
| FStar_Pervasives_Native.None -> begin
EUnit
end
| FStar_Pervasives_Native.Some (e31) -> begin
(translate_expr env e31)
end)
in ((uu____5439), (uu____5440), (uu____5441)))))
in EIfThenElse (uu____5432))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____5443) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____5450) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____5465) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5480 = (

let uu____5493 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____5493)))
in TApp (uu____5480))
end
| uu____5498 -> begin
TQualified (lid)
end)
end
| uu____5499 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____5525 -> (match (uu____5525) with
| (pat, guard, expr) -> begin
(match ((guard = FStar_Pervasives_Native.None)) with
| true -> begin
(

let uu____5551 = (translate_pat env pat)
in (match (uu____5551) with
| (env1, pat1) -> begin
(

let uu____5562 = (translate_expr env1 expr)
in ((pat1), (uu____5562)))
end))
end
| uu____5563 -> begin
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____5576) -> begin
(

let env1 = (extend env name false)
in ((env1), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env1 = (extend env "_" false)
in ((env1), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5579, cons1), ps) -> begin
(

let uu____5596 = (FStar_List.fold_left (fun uu____5616 p1 -> (match (uu____5616) with
| (env1, acc) -> begin
(

let uu____5636 = (translate_pat env1 p1)
in (match (uu____5636) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____5596) with
| (env1, ps1) -> begin
((env1), (PCons (((cons1), ((FStar_List.rev ps1))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____5665, ps) -> begin
(

let uu____5683 = (FStar_List.fold_left (fun uu____5717 uu____5718 -> (match (((uu____5717), (uu____5718))) with
| ((env1, acc), (field, p1)) -> begin
(

let uu____5787 = (translate_pat env1 p1)
in (match (uu____5787) with
| (env2, p2) -> begin
((env2), ((((field), (p2)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____5683) with
| (env1, ps1) -> begin
((env1), (PRecord ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____5849 = (FStar_List.fold_left (fun uu____5869 p1 -> (match (uu____5869) with
| (env1, acc) -> begin
(

let uu____5889 = (translate_pat env1 p1)
in (match (uu____5889) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____5849) with
| (env1, ps1) -> begin
((env1), (PTuple ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____5916) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____5921) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____5931)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____5946) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____5947) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (uu____5948) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____5949) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (uu____5952, FStar_Pervasives_Native.None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____5969 = (

let uu____5976 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____5976)))
in EApp (uu____5969)))




