
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
| uu____299 -> begin
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
| uu____347 -> begin
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
| uu____401 -> begin
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
| uu____442 -> begin
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
| uu____494 -> begin
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
| uu____541 -> begin
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
| uu____594 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____598 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____602 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____606 -> begin
false
end))


let uu___is_NoExtract : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____610 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____614 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____618 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____622 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____626 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____631 -> begin
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
| uu____646 -> begin
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
| uu____669 -> begin
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
| uu____686 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____694 -> begin
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
| uu____718 -> begin
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
| uu____742 -> begin
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
| uu____764 -> begin
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
| uu____781 -> begin
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
| uu____802 -> begin
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
| uu____825 -> begin
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
| uu____846 -> begin
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
| uu____869 -> begin
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
| uu____892 -> begin
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
| uu____924 -> begin
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
| uu____953 -> begin
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
| uu____973 -> begin
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
| uu____990 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____994 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____999 -> begin
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
| uu____1010 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____1014 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____1019 -> begin
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
| uu____1036 -> begin
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
| uu____1066 -> begin
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
| uu____1089 -> begin
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
| uu____1110 -> begin
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
| uu____1132 -> begin
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
| uu____1151 -> begin
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
| uu____1178 -> begin
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
| uu____1199 -> begin
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
| uu____1214 -> begin
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
| uu____1234 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____1238 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____1242 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____1246 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____1250 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____1254 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____1258 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____1262 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____1266 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____1270 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____1274 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____1278 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____1282 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____1286 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____1290 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____1294 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____1298 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____1302 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____1306 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____1310 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____1314 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____1318 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____1322 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____1326 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____1330 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____1334 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____1339 -> begin
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
| uu____1351 -> begin
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
| uu____1366 -> begin
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
| uu____1388 -> begin
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
| uu____1406 -> begin
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
| uu____1426 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____1430 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____1434 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____1438 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____1442 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____1446 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____1450 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____1454 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____1458 -> begin
false
end))


let uu___is_Int : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int -> begin
true
end
| uu____1462 -> begin
false
end))


let uu___is_UInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt -> begin
true
end
| uu____1466 -> begin
false
end))


let uu___is_TInt : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TInt (_0) -> begin
true
end
| uu____1483 -> begin
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
| uu____1495 -> begin
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
| uu____1506 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____1514 -> begin
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
| uu____1534 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____1538 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____1545 -> begin
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
| uu____1562 -> begin
false
end))


let uu___is_TBound : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
true
end
| uu____1567 -> begin
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
| uu____1585 -> begin
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
| uu____1616 -> begin
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


let fst3 = (fun uu____1669 -> (match (uu____1669) with
| (x, uu____1674, uu____1675) -> begin
x
end))


let snd3 = (fun uu____1689 -> (match (uu____1689) with
| (uu____1693, x, uu____1695) -> begin
x
end))


let thd3 = (fun uu____1709 -> (match (uu____1709) with
| (uu____1713, uu____1714, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun uu___114_1719 -> (match (uu___114_1719) with
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
| uu____1721 -> begin
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun uu___115_1725 -> (match (uu___115_1725) with
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
| uu____1727 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun uu___116_1735 -> (match (uu___116_1735) with
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
| uu____1737 -> begin
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

let uu___121_1804 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = uu___121_1804.names_t; module_name = uu___121_1804.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___122_1811 = env
in {names = uu___122_1811.names; names_t = (x)::env.names_t; module_name = uu___122_1811.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____1818 = (FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)
in (match (uu____1818) with
| Some (name) -> begin
name
end
| None -> begin
(failwith "internal error: name not found")
end)))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (

let uu____1828 = (find_name env x)
in uu____1828.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| uu____1838 -> begin
(

let uu____1839 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____1839))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| uu____1849 -> begin
(

let uu____1850 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____1850))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env uu____1880 -> (match (uu____1880) with
| ((name, uu____1886), uu____1887) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____1978 -> (match (uu____1978) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____2009 = m
in (match (uu____2009) with
| ((prefix, final), uu____2021, uu____2022) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
(

let uu____2038 = (translate_module m)
in Some (uu____2038));
)
end)
with
| e -> begin
((

let uu____2043 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____2043));
None;
)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____2044 -> (match (uu____2044) with
| (module_name, modul, uu____2056) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| uu____2080 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun uu___117_2088 -> (match (uu___117_2088) with
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
| uu____2092 -> begin
None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___118_2140 -> (match (uu___118_2140) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____2141 -> begin
false
end)) flags)
in (

let env = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____2143 -> begin
env
end)
in (

let rec find_return_type = (fun uu___119_2147 -> (match (uu___119_2147) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2148, uu____2149, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (

let uu____2153 = (find_return_type t0)
in (translate_type env uu____2153))
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

let uu____2165 = (

let uu____2166 = (

let uu____2174 = (translate_type env t0)
in ((None), (name), (uu____2174)))
in DExternal (uu____2166))
in Some (uu____2165))
end
| uu____2179 -> begin
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

let uu____2194 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) uu____2194));
Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort))));
)
end
end)))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2205); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2207; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = uu____2209})::[]) -> begin
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

let uu____2235 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) uu____2235));
Some (DGlobal (((flags), (name), (t), (EAny))));
)
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2241, uu____2242, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2244); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2246; FStar_Extraction_ML_Syntax.mllb_def = uu____2247; FStar_Extraction_ML_Syntax.print_typ = uu____2248})::uu____2249) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
(match (ts) with
| Some (idents, t) -> begin
(

let uu____2259 = (

let uu____2260 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " uu____2260))
in (

let uu____2264 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" uu____2259 uu____2264)))
end
| None -> begin
()
end);
None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2266) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2268) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env uu____2300 -> (match (uu____2300) with
| (name, uu____2304) -> begin
(extend_t env name)
end)) env args)
in (match (assumed) with
| true -> begin
None
end
| uu____2306 -> begin
(

let uu____2307 = (

let uu____2308 = (

let uu____2315 = (translate_type env t)
in ((name), ((FStar_List.length args)), (uu____2315)))
in DTypeAlias (uu____2308))
in Some (uu____2307))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2321, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env uu____2355 -> (match (uu____2355) with
| (name, uu____2359) -> begin
(extend_t env name)
end)) env args)
in (

let uu____2360 = (

let uu____2361 = (

let uu____2373 = (FStar_List.map (fun uu____2385 -> (match (uu____2385) with
| (f, t) -> begin
(

let uu____2394 = (

let uu____2397 = (translate_type env t)
in ((uu____2397), (false)))
in ((f), (uu____2394)))
end)) fields)
in ((name), ((FStar_List.length args)), (uu____2373)))
in DTypeFlat (uu____2361))
in Some (uu____2360))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2410, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env uu____2445 -> (match (uu____2445) with
| (name, uu____2449) -> begin
(extend_t env name)
end)) env args)
in (

let uu____2450 = (

let uu____2451 = (

let uu____2466 = (FStar_List.mapi (fun i uu____2486 -> (match (uu____2486) with
| (cons, ts) -> begin
(

let uu____2501 = (FStar_List.mapi (fun j t -> (

let uu____2513 = (

let uu____2514 = (FStar_Util.string_of_int i)
in (

let uu____2515 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "x%s%s" uu____2514 uu____2515)))
in (

let uu____2516 = (

let uu____2519 = (translate_type env t)
in ((uu____2519), (false)))
in ((uu____2513), (uu____2516))))) ts)
in ((cons), (uu____2501)))
end)) branches)
in ((name), ((FStar_List.length args)), (uu____2466)))
in DTypeVariant (uu____2451))
in Some (uu____2450))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2540, name, _mangled_name, uu____2543, uu____2544))::uu____2545) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
((FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations");
None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____2567) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____2569) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, uu____2577) -> begin
(

let uu____2578 = (find_t env name)
in TBound (uu____2578))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____2580, t2) -> begin
(

let uu____2582 = (

let uu____2585 = (translate_type env t1)
in (

let uu____2586 = (translate_type env t2)
in ((uu____2585), (uu____2586))))
in TArrow (uu____2582))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____2589 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2589 = "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____2592 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2592 = "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____2599 = (FStar_Util.must (mk_width m))
in TInt (uu____2599))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____2606 = (FStar_Util.must (mk_width m))
in TInt (uu____2606))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____2610 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2610 = "FStar.Buffer.buffer")) -> begin
(

let uu____2611 = (translate_type env arg)
in TBuf (uu____2611))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____2612)::[], p) when (

let uu____2615 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2615 = "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (("Prims")::[], t)) when (FStar_Util.starts_with t "tuple") -> begin
(

let uu____2633 = (FStar_List.map (translate_type env) args)
in TTuple (uu____2633))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2642 = (

let uu____2649 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____2649)))
in TApp (uu____2642))
end
| uu____2652 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____2655 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____2655))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____2665 -> (match (uu____2665) with
| ((name, uu____2669), typ) -> begin
(

let uu____2673 = (translate_type env typ)
in {name = name; typ = uu____2673; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____2678) -> begin
(

let uu____2679 = (find env name)
in EBound (uu____2679))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____2683 = (

let uu____2686 = (FStar_Util.must (mk_op op))
in (

let uu____2687 = (FStar_Util.must (mk_width m))
in ((uu____2686), (uu____2687))))
in EOp (uu____2683))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____2690 = (

let uu____2693 = (FStar_Util.must (mk_bool_op op))
in ((uu____2693), (Bool)))
in EOp (uu____2690))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2698); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun uu___120_2714 -> (match (uu___120_2714) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| uu____2715 -> begin
false
end)) flags)
in (

let uu____2716 = (match (is_mut) with
| true -> begin
(

let uu____2721 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when (

let uu____2725 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2725 = "FStar.ST.stackref")) -> begin
t
end
| uu____2726 -> begin
(

let uu____2727 = (

let uu____2728 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" uu____2728))
in (failwith uu____2727))
end)
in (

let uu____2730 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (uu____2731, (body)::[]); FStar_Extraction_ML_Syntax.mlty = uu____2733; FStar_Extraction_ML_Syntax.loc = uu____2734} -> begin
body
end
| uu____2736 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((uu____2721), (uu____2730))))
end
| uu____2737 -> begin
((typ), (body))
end)
in (match (uu____2716) with
| (typ, body) -> begin
(

let binder = (

let uu____2741 = (translate_type env typ)
in {name = name; typ = uu____2741; mut = is_mut})
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

let uu____2757 = (

let uu____2763 = (translate_expr env expr)
in (

let uu____2764 = (translate_branches env branches)
in ((uu____2763), (uu____2764))))
in EMatch (uu____2757))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2772; FStar_Extraction_ML_Syntax.loc = uu____2773}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, uu____2775); FStar_Extraction_ML_Syntax.mlty = uu____2776; FStar_Extraction_ML_Syntax.loc = uu____2777})::[]) when ((

let uu____2779 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2779 = "FStar.ST.op_Bang")) && (is_mutable env v)) -> begin
(

let uu____2780 = (find env v)
in EBound (uu____2780))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2782; FStar_Extraction_ML_Syntax.loc = uu____2783}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, uu____2785); FStar_Extraction_ML_Syntax.mlty = uu____2786; FStar_Extraction_ML_Syntax.loc = uu____2787})::(e)::[]) when ((

let uu____2790 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2790 = "FStar.ST.op_Colon_Equals")) && (is_mutable env v)) -> begin
(

let uu____2791 = (

let uu____2794 = (

let uu____2795 = (find env v)
in EBound (uu____2795))
in (

let uu____2796 = (translate_expr env e)
in ((uu____2794), (uu____2796))))
in EAssign (uu____2791))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2798; FStar_Extraction_ML_Syntax.loc = uu____2799}, (e1)::(e2)::[]) when ((

let uu____2803 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2803 = "FStar.Buffer.index")) || (

let uu____2804 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2804 = "FStar.Buffer.op_Array_Access"))) -> begin
(

let uu____2805 = (

let uu____2808 = (translate_expr env e1)
in (

let uu____2809 = (translate_expr env e2)
in ((uu____2808), (uu____2809))))
in EBufRead (uu____2805))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2811; FStar_Extraction_ML_Syntax.loc = uu____2812}, (e1)::(e2)::[]) when (

let uu____2816 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2816 = "FStar.Buffer.create")) -> begin
(

let uu____2817 = (

let uu____2821 = (translate_expr env e1)
in (

let uu____2822 = (translate_expr env e2)
in ((Stack), (uu____2821), (uu____2822))))
in EBufCreate (uu____2817))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2824; FStar_Extraction_ML_Syntax.loc = uu____2825}, (_e0)::(e1)::(e2)::[]) when (

let uu____2830 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2830 = "FStar.Buffer.rcreate")) -> begin
(

let uu____2831 = (

let uu____2835 = (translate_expr env e1)
in (

let uu____2836 = (translate_expr env e2)
in ((Eternal), (uu____2835), (uu____2836))))
in EBufCreate (uu____2831))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2838; FStar_Extraction_ML_Syntax.loc = uu____2839}, (e2)::[]) when (

let uu____2842 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2842 = "FStar.Buffer.createL")) -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| uu____2866 -> begin
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (

let uu____2872 = (

let uu____2876 = (

let uu____2878 = (list_elements e2)
in (FStar_List.map (translate_expr env) uu____2878))
in ((Stack), (uu____2876)))
in EBufCreateL (uu____2872))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2882; FStar_Extraction_ML_Syntax.loc = uu____2883}, (e1)::(e2)::(_e3)::[]) when (

let uu____2888 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2888 = "FStar.Buffer.sub")) -> begin
(

let uu____2889 = (

let uu____2892 = (translate_expr env e1)
in (

let uu____2893 = (translate_expr env e2)
in ((uu____2892), (uu____2893))))
in EBufSub (uu____2889))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2895; FStar_Extraction_ML_Syntax.loc = uu____2896}, (e1)::(e2)::[]) when (

let uu____2900 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2900 = "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2902; FStar_Extraction_ML_Syntax.loc = uu____2903}, (e1)::(e2)::[]) when (

let uu____2907 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2907 = "FStar.Buffer.offset")) -> begin
(

let uu____2908 = (

let uu____2911 = (translate_expr env e1)
in (

let uu____2912 = (translate_expr env e2)
in ((uu____2911), (uu____2912))))
in EBufSub (uu____2908))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2914; FStar_Extraction_ML_Syntax.loc = uu____2915}, (e1)::(e2)::(e3)::[]) when ((

let uu____2920 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2920 = "FStar.Buffer.upd")) || (

let uu____2921 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2921 = "FStar.Buffer.op_Array_Assignment"))) -> begin
(

let uu____2922 = (

let uu____2926 = (translate_expr env e1)
in (

let uu____2927 = (translate_expr env e2)
in (

let uu____2928 = (translate_expr env e3)
in ((uu____2926), (uu____2927), (uu____2928)))))
in EBufWrite (uu____2922))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2930; FStar_Extraction_ML_Syntax.loc = uu____2931}, (uu____2932)::[]) when (

let uu____2934 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2934 = "FStar.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2936; FStar_Extraction_ML_Syntax.loc = uu____2937}, (uu____2938)::[]) when (

let uu____2940 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2940 = "FStar.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2942; FStar_Extraction_ML_Syntax.loc = uu____2943}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (

let uu____2950 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2950 = "FStar.Buffer.blit")) -> begin
(

let uu____2951 = (

let uu____2957 = (translate_expr env e1)
in (

let uu____2958 = (translate_expr env e2)
in (

let uu____2959 = (translate_expr env e3)
in (

let uu____2960 = (translate_expr env e4)
in (

let uu____2961 = (translate_expr env e5)
in ((uu____2957), (uu____2958), (uu____2959), (uu____2960), (uu____2961)))))))
in EBufBlit (uu____2951))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2963; FStar_Extraction_ML_Syntax.loc = uu____2964}, (e1)::(e2)::(e3)::[]) when (

let uu____2969 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2969 = "FStar.Buffer.fill")) -> begin
(

let uu____2970 = (

let uu____2974 = (translate_expr env e1)
in (

let uu____2975 = (translate_expr env e2)
in (

let uu____2976 = (translate_expr env e3)
in ((uu____2974), (uu____2975), (uu____2976)))))
in EBufFill (uu____2970))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2978; FStar_Extraction_ML_Syntax.loc = uu____2979}, (uu____2980)::[]) when (

let uu____2982 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2982 = "FStar.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2984; FStar_Extraction_ML_Syntax.loc = uu____2985}, (e)::[]) when (

let uu____2988 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2988 = "Obj.repr")) -> begin
(

let uu____2989 = (

let uu____2992 = (translate_expr env e)
in ((uu____2992), (TAny)))
in ECast (uu____2989))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____2995; FStar_Extraction_ML_Syntax.loc = uu____2996}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____3001 = (FStar_Util.must (mk_width m))
in (

let uu____3002 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____3001 uu____3002 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____3004; FStar_Extraction_ML_Syntax.loc = uu____3005}, args) when (is_bool_op op) -> begin
(

let uu____3010 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____3010 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(

let uu____3035 = (

let uu____3038 = (FStar_Util.must (mk_width m))
in ((uu____3038), (c)))
in EConstant (uu____3035))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____3039; FStar_Extraction_ML_Syntax.loc = uu____3040}, ({FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.mlty = uu____3042; FStar_Extraction_ML_Syntax.loc = uu____3043})::[]) -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____3047 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____3049; FStar_Extraction_ML_Syntax.loc = uu____3050}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____3055 = (

let uu____3058 = (translate_expr env arg)
in ((uu____3058), (TInt (UInt64))))
in ECast (uu____3055))
end
| uu____3059 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____3060 = (

let uu____3063 = (translate_expr env arg)
in ((uu____3063), (TInt (UInt32))))
in ECast (uu____3060))
end
| uu____3064 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____3065 = (

let uu____3068 = (translate_expr env arg)
in ((uu____3068), (TInt (UInt16))))
in ECast (uu____3065))
end
| uu____3069 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____3070 = (

let uu____3073 = (translate_expr env arg)
in ((uu____3073), (TInt (UInt8))))
in ECast (uu____3070))
end
| uu____3074 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____3075 = (

let uu____3078 = (translate_expr env arg)
in ((uu____3078), (TInt (Int64))))
in ECast (uu____3075))
end
| uu____3079 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____3080 = (

let uu____3083 = (translate_expr env arg)
in ((uu____3083), (TInt (Int32))))
in ECast (uu____3080))
end
| uu____3084 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____3085 = (

let uu____3088 = (translate_expr env arg)
in ((uu____3088), (TInt (Int16))))
in ECast (uu____3085))
end
| uu____3089 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____3090 = (

let uu____3093 = (translate_expr env arg)
in ((uu____3093), (TInt (Int8))))
in ECast (uu____3090))
end
| uu____3094 -> begin
(

let uu____3095 = (

let uu____3099 = (

let uu____3101 = (translate_expr env arg)
in (uu____3101)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____3099)))
in EApp (uu____3095))
end)
end)
end)
end)
end)
end)
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = uu____3106; FStar_Extraction_ML_Syntax.loc = uu____3107}, args) -> begin
(

let uu____3113 = (

let uu____3117 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (uu____3117)))
in EApp (uu____3113))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(

let uu____3124 = (

let uu____3127 = (translate_expr env e)
in (

let uu____3128 = (translate_type env t_to)
in ((uu____3127), (uu____3128))))
in ECast (uu____3124))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____3129, fields) -> begin
(

let uu____3139 = (

let uu____3145 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3146 = (FStar_List.map (fun uu____3154 -> (match (uu____3154) with
| (field, expr) -> begin
(

let uu____3161 = (translate_expr env expr)
in ((field), (uu____3161)))
end)) fields)
in ((uu____3145), (uu____3146))))
in EFlat (uu____3139))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(

let uu____3167 = (

let uu____3171 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3172 = (translate_expr env e)
in ((uu____3171), (uu____3172), ((Prims.snd path)))))
in EField (uu____3167))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____3174) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, uu____3182) -> begin
(

let uu____3185 = (

let uu____3186 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____3186))
in (failwith uu____3185))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____3190 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____3190))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____3194 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____3194))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3196, cons), es) -> begin
(

let uu____3206 = (

let uu____3211 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3212 = (FStar_List.map (translate_expr env) es)
in ((uu____3211), (cons), (uu____3212))))
in ECons (uu____3206))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let uu____3226 = (

let uu____3230 = (translate_expr env body)
in ((binders), (uu____3230)))
in EFun (uu____3226))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____3237 = (

let uu____3241 = (translate_expr env e1)
in (

let uu____3242 = (translate_expr env e2)
in (

let uu____3243 = (match (e3) with
| None -> begin
EUnit
end
| Some (e3) -> begin
(translate_expr env e3)
end)
in ((uu____3241), (uu____3242), (uu____3243)))))
in EIfThenElse (uu____3237))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____3245) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____3249) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____3257) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3270 = (

let uu____3277 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____3277)))
in TApp (uu____3270))
end
| uu____3280 -> begin
TQualified (lid)
end)
end
| uu____3281 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____3296 -> (match (uu____3296) with
| (pat, guard, expr) -> begin
(match ((guard = None)) with
| true -> begin
(

let uu____3311 = (translate_pat env pat)
in (match (uu____3311) with
| (env, pat) -> begin
(

let uu____3318 = (translate_expr env expr)
in ((pat), (uu____3318)))
end))
end
| uu____3319 -> begin
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____3328) -> begin
(

let env = (extend env name false)
in ((env), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env = (extend env "_" false)
in ((env), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3331, cons), ps) -> begin
(

let uu____3341 = (FStar_List.fold_left (fun uu____3348 p -> (match (uu____3348) with
| (env, acc) -> begin
(

let uu____3360 = (translate_pat env p)
in (match (uu____3360) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3341) with
| (env, ps) -> begin
((env), (PCons (((cons), ((FStar_List.rev ps))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____3377, ps) -> begin
(

let uu____3387 = (FStar_List.fold_left (fun uu____3400 uu____3401 -> (match (((uu____3400), (uu____3401))) with
| ((env, acc), (field, p)) -> begin
(

let uu____3438 = (translate_pat env p)
in (match (uu____3438) with
| (env, p) -> begin
((env), ((((field), (p)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3387) with
| (env, ps) -> begin
((env), (PRecord ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____3472 = (FStar_List.fold_left (fun uu____3479 p -> (match (uu____3479) with
| (env, acc) -> begin
(

let uu____3491 = (translate_pat env p)
in (match (uu____3491) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3472) with
| (env, ps) -> begin
((env), (PTuple ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____3507) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____3510) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (uu____3517)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____3525) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____3526) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (uu____3527) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____3528) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (uu____3530, None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____3541 = (

let uu____3545 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____3545)))
in EApp (uu____3541)))




