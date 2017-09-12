
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
| uu____506 -> begin
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
| uu____594 -> begin
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
| uu____698 -> begin
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
| uu____770 -> begin
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
| uu____864 -> begin
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
| uu____948 -> begin
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
| uu____1045 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____1050 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____1055 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1060 -> begin
false
end))


let uu___is_NoExtract : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____1065 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1070 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1075 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____1080 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____1085 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____1091 -> begin
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
| uu____1111 -> begin
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
| uu____1147 -> begin
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
| uu____1172 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____1184 -> begin
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
| uu____1222 -> begin
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
| uu____1260 -> begin
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
| uu____1294 -> begin
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
| uu____1318 -> begin
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
| uu____1350 -> begin
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
| uu____1386 -> begin
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
| uu____1418 -> begin
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
| uu____1454 -> begin
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
| uu____1490 -> begin
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
| uu____1544 -> begin
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
| uu____1592 -> begin
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
| uu____1622 -> begin
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
| uu____1647 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____1652 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____1658 -> begin
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
| uu____1671 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____1676 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____1682 -> begin
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
| uu____1706 -> begin
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
| uu____1756 -> begin
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
| uu____1792 -> begin
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
| uu____1824 -> begin
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
| uu____1858 -> begin
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
| uu____1886 -> begin
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
| uu____1930 -> begin
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
| uu____1962 -> begin
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
| uu____1984 -> begin
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
| uu____2022 -> begin
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
| uu____2035 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____2040 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____2045 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____2050 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____2055 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____2060 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____2065 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____2070 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____2075 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____2080 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____2085 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____2090 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____2095 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____2100 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____2105 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____2110 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____2115 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____2120 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____2125 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____2130 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____2135 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____2140 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____2145 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____2150 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____2155 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____2160 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____2166 -> begin
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
| uu____2180 -> begin
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
| uu____2200 -> begin
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
| uu____2234 -> begin
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
| uu____2260 -> begin
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
| uu____2291 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____2296 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____2301 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____2306 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____2311 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____2316 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____2321 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____2326 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____2331 -> begin
false
end))


let uu___is_Int : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int -> begin
true
end
| uu____2336 -> begin
false
end))


let uu___is_UInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt -> begin
true
end
| uu____2341 -> begin
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
| uu____2368 -> begin
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
| uu____2382 -> begin
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
| uu____2395 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____2407 -> begin
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
| uu____2438 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____2443 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____2453 -> begin
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
| uu____2478 -> begin
false
end))


let uu___is_TBound : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
true
end
| uu____2484 -> begin
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
| uu____2510 -> begin
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
| uu____2562 -> begin
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


let fst3 : 'Auu____2643 'Auu____2644 'Auu____2645 . ('Auu____2645 * 'Auu____2644 * 'Auu____2643)  ->  'Auu____2645 = (fun uu____2655 -> (match (uu____2655) with
| (x, uu____2663, uu____2664) -> begin
x
end))


let snd3 : 'Auu____2673 'Auu____2674 'Auu____2675 . ('Auu____2675 * 'Auu____2674 * 'Auu____2673)  ->  'Auu____2674 = (fun uu____2685 -> (match (uu____2685) with
| (uu____2692, x, uu____2694) -> begin
x
end))


let thd3 : 'Auu____2703 'Auu____2704 'Auu____2705 . ('Auu____2705 * 'Auu____2704 * 'Auu____2703)  ->  'Auu____2703 = (fun uu____2715 -> (match (uu____2715) with
| (uu____2722, uu____2723, x) -> begin
x
end))


let mk_width : Prims.string  ->  width FStar_Pervasives_Native.option = (fun uu___124_2730 -> (match (uu___124_2730) with
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
| uu____2733 -> begin
FStar_Pervasives_Native.None
end))


let mk_bool_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___125_2739 -> (match (uu___125_2739) with
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
| uu____2742 -> begin
FStar_Pervasives_Native.None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> FStar_Pervasives_Native.None))


let mk_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___126_2754 -> (match (uu___126_2754) with
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
| uu____2757 -> begin
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

let uu___131_2879 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = uu___131_2879.names_t; module_name = uu___131_2879.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___132_2888 = env
in {names = uu___132_2888.names; names_t = (x)::env.names_t; module_name = uu___132_2888.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____2897 = (FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)
in (match (uu____2897) with
| FStar_Pervasives_Native.Some (name) -> begin
name
end
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: name not found")
end)))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (

let uu____2911 = (find_name env x)
in uu____2911.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| uu____2928 -> begin
(

let uu____2929 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____2929))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| uu____2946 -> begin
(

let uu____2947 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____2947))
end)


let add_binders : 'Auu____2956 'Auu____2957 . env  ->  ((Prims.string * 'Auu____2957) * 'Auu____2956) Prims.list  ->  env = (fun env binders -> (FStar_List.fold_left (fun env1 uu____3000 -> (match (uu____3000) with
| ((name, uu____3010), uu____3011) -> begin
(extend env1 name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____3140 -> (match (uu____3140) with
| FStar_Extraction_ML_Syntax.MLLib (modules1) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____3200 = m
in (match (uu____3200) with
| ((prefix1, final), uu____3221, uu____3222) -> begin
(FStar_String.concat "." (FStar_List.append prefix1 ((final)::[])))
end))
in try
(match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
(

let uu____3254 = (translate_module m)
in FStar_Pervasives_Native.Some (uu____3254));
)
end)
with
| e -> begin
((

let uu____3263 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____3263));
FStar_Pervasives_Native.None;
)
end)) modules1)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____3264 -> (match (uu____3264) with
| (module_name, modul, uu____3285) -> begin
(

let module_name1 = (FStar_List.append (FStar_Pervasives_Native.fst module_name) (((FStar_Pervasives_Native.snd module_name))::[]))
in (

let program = (match (modul) with
| FStar_Pervasives_Native.Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name1)) decls)
end
| uu____3328 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name1)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun uu___127_3343 -> (match (uu___127_3343) with
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
| uu____3348 -> begin
FStar_Pervasives_Native.None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl FStar_Pervasives_Native.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3356); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3359; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____3362; FStar_Extraction_ML_Syntax.loc = uu____3363}; FStar_Extraction_ML_Syntax.print_typ = uu____3364})::[]) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___128_3385 -> (match (uu___128_3385) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____3386 -> begin
false
end)) flags)
in (

let env1 = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____3388 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 uu____3399 -> (match (uu____3399) with
| (name1, uu____3405) -> begin
(extend_t env2 name1)
end)) env1 tvars)
in (

let rec find_return_type = (fun i uu___129_3412 -> (match (uu___129_3412) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3413, uu____3414, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type (i - (Prims.parse_int "1")) t)
end
| t -> begin
t
end))
in (

let t = (

let uu____3418 = (find_return_type (FStar_List.length args) t0)
in (translate_type env2 uu____3418))
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

let uu____3443 = (

let uu____3444 = (

let uu____3459 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (name1), (uu____3459)))
in DExternal (uu____3444))
in FStar_Pervasives_Native.Some (uu____3443))
end
| uu____3468 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____3469 -> begin
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

let uu____3498 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____3498));
FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (EAbort))));
)
end
end))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3516); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3519; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____3522; FStar_Extraction_ML_Syntax.loc = uu____3523}, uu____3524, uu____3525); FStar_Extraction_ML_Syntax.mlty = uu____3526; FStar_Extraction_ML_Syntax.loc = uu____3527}; FStar_Extraction_ML_Syntax.print_typ = uu____3528})::[]) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___128_3549 -> (match (uu___128_3549) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____3550 -> begin
false
end)) flags)
in (

let env1 = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____3552 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 uu____3563 -> (match (uu____3563) with
| (name1, uu____3569) -> begin
(extend_t env2 name1)
end)) env1 tvars)
in (

let rec find_return_type = (fun i uu___129_3576 -> (match (uu___129_3576) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3577, uu____3578, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type (i - (Prims.parse_int "1")) t)
end
| t -> begin
t
end))
in (

let t = (

let uu____3582 = (find_return_type (FStar_List.length args) t0)
in (translate_type env2 uu____3582))
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

let uu____3607 = (

let uu____3608 = (

let uu____3623 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (name1), (uu____3623)))
in DExternal (uu____3608))
in FStar_Pervasives_Native.Some (uu____3607))
end
| uu____3632 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____3633 -> begin
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

let uu____3662 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____3662));
FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (EAbort))));
)
end
end))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3680); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3682; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = uu____3684})::[]) -> begin
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

let uu____3732 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____3732));
FStar_Pervasives_Native.Some (DGlobal (((flags1), (name1), (t1), (EAny))));
)
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____3743, uu____3744, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____3746); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3748; FStar_Extraction_ML_Syntax.mllb_def = uu____3749; FStar_Extraction_ML_Syntax.print_typ = uu____3750})::uu____3751) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
(match (ts) with
| FStar_Pervasives_Native.Some (idents, t) -> begin
(

let uu____3766 = (

let uu____3767 = (FStar_List.map FStar_Pervasives_Native.fst idents)
in (FStar_String.concat ", " uu____3767))
in (

let uu____3774 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" uu____3766 uu____3774)))
end
| FStar_Pervasives_Native.None -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____3777) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____3780) -> begin
FStar_Pervasives_Native.None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, uu____3785, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____3844 -> (match (uu____3844) with
| (name2, uu____3850) -> begin
(extend_t env1 name2)
end)) env args)
in (match (assumed) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3853 -> begin
(

let uu____3854 = (

let uu____3855 = (

let uu____3868 = (translate_type env1 t)
in ((name1), ((FStar_List.length args)), (uu____3868)))
in DTypeAlias (uu____3855))
in FStar_Pervasives_Native.Some (uu____3854))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____3875, name, _mangled_name, args, uu____3879, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____3944 -> (match (uu____3944) with
| (name2, uu____3950) -> begin
(extend_t env1 name2)
end)) env args)
in (

let uu____3951 = (

let uu____3952 = (

let uu____3975 = (FStar_List.map (fun uu____4002 -> (match (uu____4002) with
| (f, t) -> begin
(

let uu____4017 = (

let uu____4022 = (translate_type env1 t)
in ((uu____4022), (false)))
in ((f), (uu____4017)))
end)) fields)
in ((name1), ((FStar_List.length args)), (uu____3975)))
in DTypeFlat (uu____3952))
in FStar_Pervasives_Native.Some (uu____3951))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____4043, name, _mangled_name, args, uu____4047, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____4118 -> (match (uu____4118) with
| (name2, uu____4124) -> begin
(extend_t env1 name2)
end)) env args)
in (

let uu____4125 = (

let uu____4126 = (

let uu____4155 = (FStar_List.map (fun uu____4200 -> (match (uu____4200) with
| (cons1, ts) -> begin
(

let uu____4239 = (FStar_List.map (fun uu____4266 -> (match (uu____4266) with
| (name2, t) -> begin
(

let uu____4281 = (

let uu____4286 = (translate_type env1 t)
in ((uu____4286), (false)))
in ((name2), (uu____4281)))
end)) ts)
in ((cons1), (uu____4239)))
end)) branches)
in ((name1), ((FStar_List.length args)), (uu____4155)))
in DTypeVariant (uu____4126))
in FStar_Pervasives_Native.Some (uu____4125))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____4323, name, _mangled_name, uu____4326, uu____4327, uu____4328))::uu____4329) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
((FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations");
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____4374) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____4377) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Tuple ([]) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, uu____4393) -> begin
(

let uu____4394 = (find_t env name)
in TBound (uu____4394))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____4396, t2) -> begin
(

let uu____4398 = (

let uu____4403 = (translate_type env t1)
in (

let uu____4404 = (translate_type env t2)
in ((uu____4403), (uu____4404))))
in TArrow (uu____4398))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____4408 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4408 = "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____4412 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4412 = "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____4424 = (FStar_Util.must (mk_width m))
in TInt (uu____4424))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____4436 = (FStar_Util.must (mk_width m))
in TInt (uu____4436))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____4441 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4441 = "FStar.Monotonic.HyperStack.mem")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____4446 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4446 = "FStar.Buffer.buffer")) -> begin
(

let uu____4447 = (translate_type env arg)
in TBuf (uu____4447))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____4448)::[], p) when (

let uu____4452 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4452 = "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when (((ns = ("Prims")::[]) || (ns = ("FStar")::("Pervasives")::("Native")::[])) && (FStar_Util.starts_with t1 "tuple")) -> begin
(

let uu____4490 = (FStar_List.map (translate_type env) args)
in TTuple (uu____4490))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4499 = (

let uu____4512 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____4512)))
in TApp (uu____4499))
end
| uu____4517 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____4521 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____4521))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____4537 -> (match (uu____4537) with
| ((name, uu____4543), typ) -> begin
(

let uu____4549 = (translate_type env typ)
in {name = name; typ = uu____4549; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____4554) -> begin
(

let uu____4555 = (find env name)
in EBound (uu____4555))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____4560 = (

let uu____4565 = (FStar_Util.must (mk_op op))
in (

let uu____4566 = (FStar_Util.must (mk_width m))
in ((uu____4565), (uu____4566))))
in EOp (uu____4560))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____4570 = (

let uu____4575 = (FStar_Util.must (mk_bool_op op))
in ((uu____4575), (Bool)))
in EOp (uu____4570))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n1) -> begin
EQualified (n1)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____4580); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print7})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun uu___130_4606 -> (match (uu___130_4606) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| uu____4607 -> begin
false
end)) flags)
in (

let uu____4608 = (match (is_mut) with
| true -> begin
(

let uu____4617 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when (

let uu____4622 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4622 = "FStar.ST.stackref")) -> begin
t
end
| uu____4623 -> begin
(

let uu____4624 = (

let uu____4625 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" uu____4625))
in (failwith uu____4624))
end)
in (

let uu____4628 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (uu____4629, (body1)::[]); FStar_Extraction_ML_Syntax.mlty = uu____4631; FStar_Extraction_ML_Syntax.loc = uu____4632} -> begin
body1
end
| uu____4635 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((uu____4617), (uu____4628))))
end
| uu____4636 -> begin
((typ), (body))
end)
in (match (uu____4608) with
| (typ1, body1) -> begin
(

let binder = (

let uu____4640 = (translate_type env typ1)
in {name = name; typ = uu____4640; mut = is_mut})
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

let uu____4666 = (

let uu____4677 = (translate_expr env expr)
in (

let uu____4678 = (translate_branches env branches)
in ((uu____4677), (uu____4678))))
in EMatch (uu____4666))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4692; FStar_Extraction_ML_Syntax.loc = uu____4693}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v1, uu____4695); FStar_Extraction_ML_Syntax.mlty = uu____4696; FStar_Extraction_ML_Syntax.loc = uu____4697})::[]) when ((

let uu____4702 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4702 = "FStar.HyperStack.ST.op_Bang")) && (is_mutable env v1)) -> begin
(

let uu____4703 = (find env v1)
in EBound (uu____4703))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4705; FStar_Extraction_ML_Syntax.loc = uu____4706}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v1, uu____4708); FStar_Extraction_ML_Syntax.mlty = uu____4709; FStar_Extraction_ML_Syntax.loc = uu____4710})::(e1)::[]) when ((

let uu____4716 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4716 = "FStar.HyperStack.ST.op_Colon_Equals")) && (is_mutable env v1)) -> begin
(

let uu____4717 = (

let uu____4722 = (

let uu____4723 = (find env v1)
in EBound (uu____4723))
in (

let uu____4724 = (translate_expr env e1)
in ((uu____4722), (uu____4724))))
in EAssign (uu____4717))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4726; FStar_Extraction_ML_Syntax.loc = uu____4727}, (e1)::(e2)::[]) when ((

let uu____4734 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4734 = "FStar.Buffer.index")) || (

let uu____4736 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4736 = "FStar.Buffer.op_Array_Access"))) -> begin
(

let uu____4737 = (

let uu____4742 = (translate_expr env e1)
in (

let uu____4743 = (translate_expr env e2)
in ((uu____4742), (uu____4743))))
in EBufRead (uu____4737))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4745; FStar_Extraction_ML_Syntax.loc = uu____4746}, (e1)::(e2)::[]) when (

let uu____4751 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4751 = "FStar.Buffer.create")) -> begin
(

let uu____4752 = (

let uu____4759 = (translate_expr env e1)
in (

let uu____4760 = (translate_expr env e2)
in ((Stack), (uu____4759), (uu____4760))))
in EBufCreate (uu____4752))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4762; FStar_Extraction_ML_Syntax.loc = uu____4763}, (_e0)::(e1)::(e2)::[]) when (

let uu____4769 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4769 = "FStar.Buffer.rcreate")) -> begin
(

let uu____4770 = (

let uu____4777 = (translate_expr env e1)
in (

let uu____4778 = (translate_expr env e2)
in ((Eternal), (uu____4777), (uu____4778))))
in EBufCreate (uu____4770))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4780; FStar_Extraction_ML_Syntax.loc = uu____4781}, (e2)::[]) when (

let uu____4785 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4785 = "FStar.Buffer.createL")) -> begin
(

let rec list_elements1 = (fun acc e21 -> (match (e21.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd1)::(tl1)::[]) -> begin
(list_elements1 ((hd1)::acc) tl1)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| uu____4823 -> begin
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements2 = (list_elements1 [])
in (

let uu____4831 = (

let uu____4838 = (

let uu____4841 = (list_elements2 e2)
in (FStar_List.map (translate_expr env) uu____4841))
in ((Stack), (uu____4838)))
in EBufCreateL (uu____4831))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4847; FStar_Extraction_ML_Syntax.loc = uu____4848}, (e1)::(e2)::(_e3)::[]) when (

let uu____4854 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4854 = "FStar.Buffer.sub")) -> begin
(

let uu____4855 = (

let uu____4860 = (translate_expr env e1)
in (

let uu____4861 = (translate_expr env e2)
in ((uu____4860), (uu____4861))))
in EBufSub (uu____4855))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4863; FStar_Extraction_ML_Syntax.loc = uu____4864}, (e1)::(e2)::[]) when (

let uu____4869 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4869 = "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4871; FStar_Extraction_ML_Syntax.loc = uu____4872}, (e1)::(e2)::[]) when (

let uu____4877 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4877 = "FStar.Buffer.offset")) -> begin
(

let uu____4878 = (

let uu____4883 = (translate_expr env e1)
in (

let uu____4884 = (translate_expr env e2)
in ((uu____4883), (uu____4884))))
in EBufSub (uu____4878))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4886; FStar_Extraction_ML_Syntax.loc = uu____4887}, (e1)::(e2)::(e3)::[]) when ((

let uu____4895 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4895 = "FStar.Buffer.upd")) || (

let uu____4897 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4897 = "FStar.Buffer.op_Array_Assignment"))) -> begin
(

let uu____4898 = (

let uu____4905 = (translate_expr env e1)
in (

let uu____4906 = (translate_expr env e2)
in (

let uu____4907 = (translate_expr env e3)
in ((uu____4905), (uu____4906), (uu____4907)))))
in EBufWrite (uu____4898))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4909; FStar_Extraction_ML_Syntax.loc = uu____4910}, (uu____4911)::[]) when (

let uu____4914 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4914 = "FStar.HyperStack.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4916; FStar_Extraction_ML_Syntax.loc = uu____4917}, (uu____4918)::[]) when (

let uu____4921 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4921 = "FStar.HyperStack.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4923; FStar_Extraction_ML_Syntax.loc = uu____4924}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (

let uu____4932 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4932 = "FStar.Buffer.blit")) -> begin
(

let uu____4933 = (

let uu____4944 = (translate_expr env e1)
in (

let uu____4945 = (translate_expr env e2)
in (

let uu____4946 = (translate_expr env e3)
in (

let uu____4947 = (translate_expr env e4)
in (

let uu____4948 = (translate_expr env e5)
in ((uu____4944), (uu____4945), (uu____4946), (uu____4947), (uu____4948)))))))
in EBufBlit (uu____4933))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4950; FStar_Extraction_ML_Syntax.loc = uu____4951}, (e1)::(e2)::(e3)::[]) when (

let uu____4957 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4957 = "FStar.Buffer.fill")) -> begin
(

let uu____4958 = (

let uu____4965 = (translate_expr env e1)
in (

let uu____4966 = (translate_expr env e2)
in (

let uu____4967 = (translate_expr env e3)
in ((uu____4965), (uu____4966), (uu____4967)))))
in EBufFill (uu____4958))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4969; FStar_Extraction_ML_Syntax.loc = uu____4970}, (uu____4971)::[]) when (

let uu____4974 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4974 = "FStar.HyperStack.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____4976; FStar_Extraction_ML_Syntax.loc = uu____4977}, (e1)::[]) when (

let uu____4981 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____4981 = "Obj.repr")) -> begin
(

let uu____4982 = (

let uu____4987 = (translate_expr env e1)
in ((uu____4987), (TAny)))
in ECast (uu____4982))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____4990; FStar_Extraction_ML_Syntax.loc = uu____4991}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____4999 = (FStar_Util.must (mk_width m))
in (

let uu____5000 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____4999 uu____5000 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____5002; FStar_Extraction_ML_Syntax.loc = uu____5003}, args) when (is_bool_op op) -> begin
(

let uu____5011 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____5011 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____5013; FStar_Extraction_ML_Syntax.loc = uu____5014}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____5016; FStar_Extraction_ML_Syntax.loc = uu____5017})::[]) when (is_machine_int m) -> begin
(

let uu____5032 = (

let uu____5037 = (FStar_Util.must (mk_width m))
in ((uu____5037), (c)))
in EConstant (uu____5032))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____5039; FStar_Extraction_ML_Syntax.loc = uu____5040}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____5042; FStar_Extraction_ML_Syntax.loc = uu____5043})::[]) when (is_machine_int m) -> begin
(

let uu____5058 = (

let uu____5063 = (FStar_Util.must (mk_width m))
in ((uu____5063), (c)))
in EConstant (uu____5058))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____5064; FStar_Extraction_ML_Syntax.loc = uu____5065}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____5067; FStar_Extraction_ML_Syntax.loc = uu____5068})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____5074 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____5076; FStar_Extraction_ML_Syntax.loc = uu____5077}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____5084 = (

let uu____5089 = (translate_expr env arg)
in ((uu____5089), (TInt (UInt64))))
in ECast (uu____5084))
end
| uu____5090 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____5091 = (

let uu____5096 = (translate_expr env arg)
in ((uu____5096), (TInt (UInt32))))
in ECast (uu____5091))
end
| uu____5097 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____5098 = (

let uu____5103 = (translate_expr env arg)
in ((uu____5103), (TInt (UInt16))))
in ECast (uu____5098))
end
| uu____5104 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____5105 = (

let uu____5110 = (translate_expr env arg)
in ((uu____5110), (TInt (UInt8))))
in ECast (uu____5105))
end
| uu____5111 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____5112 = (

let uu____5117 = (translate_expr env arg)
in ((uu____5117), (TInt (Int64))))
in ECast (uu____5112))
end
| uu____5118 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____5119 = (

let uu____5124 = (translate_expr env arg)
in ((uu____5124), (TInt (Int32))))
in ECast (uu____5119))
end
| uu____5125 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____5126 = (

let uu____5131 = (translate_expr env arg)
in ((uu____5131), (TInt (Int16))))
in ECast (uu____5126))
end
| uu____5132 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____5133 = (

let uu____5138 = (translate_expr env arg)
in ((uu____5138), (TInt (Int8))))
in ECast (uu____5133))
end
| uu____5139 -> begin
(

let uu____5140 = (

let uu____5147 = (

let uu____5150 = (translate_expr env arg)
in (uu____5150)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____5147)))
in EApp (uu____5140))
end)
end)
end)
end)
end)
end)
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = uu____5157; FStar_Extraction_ML_Syntax.loc = uu____5158}, args) -> begin
(

let uu____5168 = (

let uu____5175 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (uu____5175)))
in EApp (uu____5168))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (name, uu____5183); FStar_Extraction_ML_Syntax.mlty = uu____5184; FStar_Extraction_ML_Syntax.loc = uu____5185}, args) -> begin
(

let uu____5191 = (

let uu____5198 = (

let uu____5199 = (find env name)
in EBound (uu____5199))
in (

let uu____5200 = (FStar_List.map (translate_expr env) args)
in ((uu____5198), (uu____5200))))
in EApp (uu____5191))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) -> begin
(

let uu____5208 = (

let uu____5213 = (translate_expr env e1)
in (

let uu____5214 = (translate_type env t_to)
in ((uu____5213), (uu____5214))))
in ECast (uu____5208))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____5215, fields) -> begin
(

let uu____5233 = (

let uu____5244 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5245 = (FStar_List.map (fun uu____5264 -> (match (uu____5264) with
| (field, expr) -> begin
(

let uu____5275 = (translate_expr env expr)
in ((field), (uu____5275)))
end)) fields)
in ((uu____5244), (uu____5245))))
in EFlat (uu____5233))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) -> begin
(

let uu____5284 = (

let uu____5291 = (assert_lid env e1.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5292 = (translate_expr env e1)
in ((uu____5291), (uu____5292), ((FStar_Pervasives_Native.snd path)))))
in EField (uu____5284))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____5295) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, uu____5309) -> begin
(

let uu____5314 = (

let uu____5315 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head1)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____5315))
in (failwith uu____5314))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____5321 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____5321))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____5327 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____5327))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5330, cons1), es) -> begin
(

let uu____5347 = (

let uu____5356 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5357 = (FStar_List.map (translate_expr env) es)
in ((uu____5356), (cons1), (uu____5357))))
in ECons (uu____5347))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env1 = (add_binders env args)
in (

let uu____5380 = (

let uu____5389 = (translate_expr env1 body)
in (

let uu____5390 = (translate_type env1 body.FStar_Extraction_ML_Syntax.mlty)
in ((binders), (uu____5389), (uu____5390))))
in EFun (uu____5380))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____5400 = (

let uu____5407 = (translate_expr env e1)
in (

let uu____5408 = (translate_expr env e2)
in (

let uu____5409 = (match (e3) with
| FStar_Pervasives_Native.None -> begin
EUnit
end
| FStar_Pervasives_Native.Some (e31) -> begin
(translate_expr env e31)
end)
in ((uu____5407), (uu____5408), (uu____5409)))))
in EIfThenElse (uu____5400))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____5411) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____5418) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____5433) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5448 = (

let uu____5461 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____5461)))
in TApp (uu____5448))
end
| uu____5466 -> begin
TQualified (lid)
end)
end
| uu____5467 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____5493 -> (match (uu____5493) with
| (pat, guard, expr) -> begin
(match ((guard = FStar_Pervasives_Native.None)) with
| true -> begin
(

let uu____5519 = (translate_pat env pat)
in (match (uu____5519) with
| (env1, pat1) -> begin
(

let uu____5530 = (translate_expr env1 expr)
in ((pat1), (uu____5530)))
end))
end
| uu____5531 -> begin
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____5544) -> begin
(

let env1 = (extend env name false)
in ((env1), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env1 = (extend env "_" false)
in ((env1), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5547, cons1), ps) -> begin
(

let uu____5564 = (FStar_List.fold_left (fun uu____5584 p1 -> (match (uu____5584) with
| (env1, acc) -> begin
(

let uu____5604 = (translate_pat env1 p1)
in (match (uu____5604) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____5564) with
| (env1, ps1) -> begin
((env1), (PCons (((cons1), ((FStar_List.rev ps1))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____5633, ps) -> begin
(

let uu____5651 = (FStar_List.fold_left (fun uu____5685 uu____5686 -> (match (((uu____5685), (uu____5686))) with
| ((env1, acc), (field, p1)) -> begin
(

let uu____5755 = (translate_pat env1 p1)
in (match (uu____5755) with
| (env2, p2) -> begin
((env2), ((((field), (p2)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____5651) with
| (env1, ps1) -> begin
((env1), (PRecord ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____5817 = (FStar_List.fold_left (fun uu____5837 p1 -> (match (uu____5837) with
| (env1, acc) -> begin
(

let uu____5857 = (translate_pat env1 p1)
in (match (uu____5857) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____5817) with
| (env1, ps1) -> begin
((env1), (PTuple ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____5884) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____5889) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____5899)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____5914) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____5915) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (uu____5916) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____5917) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (uu____5920, FStar_Pervasives_Native.None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____5937 = (

let uu____5944 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____5944)))
in EApp (uu____5937)))




