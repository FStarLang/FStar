
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
| uu____348 -> begin
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
| uu____397 -> begin
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
| uu____454 -> begin
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
| uu____495 -> begin
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
| uu____547 -> begin
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
| uu____594 -> begin
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
| uu____647 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____651 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____655 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____659 -> begin
false
end))


let uu___is_NoExtract : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____663 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____667 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____671 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____675 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____679 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____684 -> begin
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
| uu____699 -> begin
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
| uu____722 -> begin
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
| uu____739 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____747 -> begin
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
| uu____771 -> begin
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
| uu____795 -> begin
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
| uu____817 -> begin
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
| uu____834 -> begin
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
| uu____855 -> begin
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
| uu____878 -> begin
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
| uu____899 -> begin
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
| uu____922 -> begin
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
| uu____945 -> begin
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
| uu____977 -> begin
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
| uu____1006 -> begin
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
| uu____1026 -> begin
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
| uu____1043 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____1047 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____1052 -> begin
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
| uu____1063 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____1067 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____1072 -> begin
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
| uu____1089 -> begin
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
| uu____1119 -> begin
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
| uu____1142 -> begin
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
| uu____1163 -> begin
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
| uu____1185 -> begin
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
| uu____1204 -> begin
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
| uu____1231 -> begin
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
| uu____1252 -> begin
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
| uu____1267 -> begin
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
| uu____1287 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____1291 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____1295 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____1299 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____1303 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____1307 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____1311 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____1315 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____1319 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____1323 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____1327 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____1331 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____1335 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____1339 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____1343 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____1347 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____1351 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____1355 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____1359 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____1363 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____1367 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____1371 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____1375 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____1379 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____1383 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____1387 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____1392 -> begin
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
| uu____1404 -> begin
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
| uu____1419 -> begin
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
| uu____1441 -> begin
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
| uu____1459 -> begin
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
| uu____1479 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____1483 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____1487 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____1491 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____1495 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____1499 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____1503 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____1507 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____1511 -> begin
false
end))


let uu___is_Int : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int -> begin
true
end
| uu____1515 -> begin
false
end))


let uu___is_UInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt -> begin
true
end
| uu____1519 -> begin
false
end))


let uu___is_TInt : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TInt (_0) -> begin
true
end
| uu____1536 -> begin
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
| uu____1548 -> begin
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
| uu____1559 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____1567 -> begin
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
| uu____1587 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____1591 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____1598 -> begin
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
| uu____1615 -> begin
false
end))


let uu___is_TBound : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
true
end
| uu____1620 -> begin
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
| uu____1638 -> begin
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
| uu____1669 -> begin
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


let fst3 = (fun uu____1722 -> (match (uu____1722) with
| (x, uu____1727, uu____1728) -> begin
x
end))


let snd3 = (fun uu____1742 -> (match (uu____1742) with
| (uu____1746, x, uu____1748) -> begin
x
end))


let thd3 = (fun uu____1762 -> (match (uu____1762) with
| (uu____1766, uu____1767, x) -> begin
x
end))


let mk_width : Prims.string  ->  width FStar_Pervasives_Native.option = (fun uu___118_1772 -> (match (uu___118_1772) with
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
| uu____1774 -> begin
FStar_Pervasives_Native.None
end))


let mk_bool_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___119_1778 -> (match (uu___119_1778) with
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
| uu____1780 -> begin
FStar_Pervasives_Native.None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> FStar_Pervasives_Native.None))


let mk_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___120_1788 -> (match (uu___120_1788) with
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
| uu____1790 -> begin
FStar_Pervasives_Native.None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> FStar_Pervasives_Native.None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> FStar_Pervasives_Native.None))

type env =
{names : name Prims.list; names_t : Prims.string Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; names_t = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let uu___125_1862 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = uu___125_1862.names_t; module_name = uu___125_1862.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___126_1869 = env
in {names = uu___126_1869.names; names_t = (x)::env.names_t; module_name = uu___126_1869.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____1876 = (FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)
in (match (uu____1876) with
| FStar_Pervasives_Native.Some (name) -> begin
name
end
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: name not found")
end)))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (

let uu____1886 = (find_name env x)
in uu____1886.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| uu____1896 -> begin
(

let uu____1897 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____1897))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| uu____1907 -> begin
(

let uu____1908 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____1908))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env1 uu____1938 -> (match (uu____1938) with
| ((name, uu____1944), uu____1945) -> begin
(extend env1 name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____2036 -> (match (uu____2036) with
| FStar_Extraction_ML_Syntax.MLLib (modules1) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____2067 = m
in (match (uu____2067) with
| ((prefix1, final), uu____2079, uu____2080) -> begin
(FStar_String.concat "." (FStar_List.append prefix1 ((final)::[])))
end))
in try
(match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
(

let uu____2096 = (translate_module m)
in FStar_Pervasives_Native.Some (uu____2096));
)
end)
with
| e -> begin
((

let uu____2101 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____2101));
FStar_Pervasives_Native.None;
)
end)) modules1)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____2102 -> (match (uu____2102) with
| (module_name, modul, uu____2114) -> begin
(

let module_name1 = (FStar_List.append (FStar_Pervasives_Native.fst module_name) (((FStar_Pervasives_Native.snd module_name))::[]))
in (

let program = (match (modul) with
| FStar_Pervasives_Native.Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name1)) decls)
end
| uu____2138 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name1)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun uu___121_2146 -> (match (uu___121_2146) with
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
| uu____2150 -> begin
FStar_Pervasives_Native.None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl FStar_Pervasives_Native.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2158); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2161; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____2164; FStar_Extraction_ML_Syntax.loc = uu____2165}; FStar_Extraction_ML_Syntax.print_typ = uu____2166})::[]) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___122_2177 -> (match (uu___122_2177) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____2178 -> begin
false
end)) flags)
in (

let env1 = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____2180 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 uu____2185 -> (match (uu____2185) with
| (name1, uu____2189) -> begin
(extend_t env2 name1)
end)) env1 tvars)
in (

let rec find_return_type = (fun uu___123_2193 -> (match (uu___123_2193) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2194, uu____2195, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (

let uu____2199 = (find_return_type t0)
in (translate_type env2 uu____2199))
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

let uu____2214 = (

let uu____2215 = (

let uu____2223 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (name1), (uu____2223)))
in DExternal (uu____2215))
in FStar_Pervasives_Native.Some (uu____2214))
end
| uu____2228 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____2229 -> begin
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

let uu____2246 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____2246));
FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (EAbort))));
)
end
end))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2259); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2262; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____2265; FStar_Extraction_ML_Syntax.loc = uu____2266}, uu____2267, uu____2268); FStar_Extraction_ML_Syntax.mlty = uu____2269; FStar_Extraction_ML_Syntax.loc = uu____2270}; FStar_Extraction_ML_Syntax.print_typ = uu____2271})::[]) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___122_2282 -> (match (uu___122_2282) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____2283 -> begin
false
end)) flags)
in (

let env1 = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____2285 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 uu____2290 -> (match (uu____2290) with
| (name1, uu____2294) -> begin
(extend_t env2 name1)
end)) env1 tvars)
in (

let rec find_return_type = (fun uu___123_2298 -> (match (uu___123_2298) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2299, uu____2300, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (

let uu____2304 = (find_return_type t0)
in (translate_type env2 uu____2304))
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

let uu____2319 = (

let uu____2320 = (

let uu____2328 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (name1), (uu____2328)))
in DExternal (uu____2320))
in FStar_Pervasives_Native.Some (uu____2319))
end
| uu____2333 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____2334 -> begin
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

let uu____2351 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____2351));
FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (flags1), ((FStar_List.length tvars)), (t), (name1), (binders), (EAbort))));
)
end
end))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2364); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2366; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = uu____2368})::[]) -> begin
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

let uu____2394 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (FStar_Pervasives_Native.snd name1) uu____2394));
FStar_Pervasives_Native.Some (DGlobal (((flags1), (name1), (t1), (EAny))));
)
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2400, uu____2401, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2403); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2405; FStar_Extraction_ML_Syntax.mllb_def = uu____2406; FStar_Extraction_ML_Syntax.print_typ = uu____2407})::uu____2408) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
(match (ts) with
| FStar_Pervasives_Native.Some (idents, t) -> begin
(

let uu____2418 = (

let uu____2419 = (FStar_List.map FStar_Pervasives_Native.fst idents)
in (FStar_String.concat ", " uu____2419))
in (

let uu____2423 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" uu____2418 uu____2423)))
end
| FStar_Pervasives_Native.None -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2425) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2427) -> begin
FStar_Pervasives_Native.None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2459 -> (match (uu____2459) with
| (name2, uu____2463) -> begin
(extend_t env1 name2)
end)) env args)
in (match (assumed) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2465 -> begin
(

let uu____2466 = (

let uu____2467 = (

let uu____2474 = (translate_type env1 t)
in ((name1), ((FStar_List.length args)), (uu____2474)))
in DTypeAlias (uu____2467))
in FStar_Pervasives_Native.Some (uu____2466))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2480, name, _mangled_name, args, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2514 -> (match (uu____2514) with
| (name2, uu____2518) -> begin
(extend_t env1 name2)
end)) env args)
in (

let uu____2519 = (

let uu____2520 = (

let uu____2532 = (FStar_List.map (fun uu____2544 -> (match (uu____2544) with
| (f, t) -> begin
(

let uu____2553 = (

let uu____2556 = (translate_type env1 t)
in ((uu____2556), (false)))
in ((f), (uu____2553)))
end)) fields)
in ((name1), ((FStar_List.length args)), (uu____2532)))
in DTypeFlat (uu____2520))
in FStar_Pervasives_Native.Some (uu____2519))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2569, name, _mangled_name, args, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2606 -> (match (uu____2606) with
| (name2, uu____2610) -> begin
(extend_t env1 name2)
end)) env args)
in (

let uu____2611 = (

let uu____2612 = (

let uu____2627 = (FStar_List.map (fun uu____2648 -> (match (uu____2648) with
| (cons1, ts) -> begin
(

let uu____2669 = (FStar_List.map (fun uu____2681 -> (match (uu____2681) with
| (name2, t) -> begin
(

let uu____2690 = (

let uu____2693 = (translate_type env1 t)
in ((uu____2693), (false)))
in ((name2), (uu____2690)))
end)) ts)
in ((cons1), (uu____2669)))
end)) branches)
in ((name1), ((FStar_List.length args)), (uu____2627)))
in DTypeVariant (uu____2612))
in FStar_Pervasives_Native.Some (uu____2611))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2714, name, _mangled_name, uu____2717, uu____2718))::uu____2719) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
((FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations");
FStar_Pervasives_Native.None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____2741) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____2743) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Tuple ([]) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, uu____2753) -> begin
(

let uu____2754 = (find_t env name)
in TBound (uu____2754))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____2756, t2) -> begin
(

let uu____2758 = (

let uu____2761 = (translate_type env t1)
in (

let uu____2762 = (translate_type env t2)
in ((uu____2761), (uu____2762))))
in TArrow (uu____2758))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____2765 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2765 = "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____2768 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2768 = "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____2775 = (FStar_Util.must (mk_width m))
in TInt (uu____2775))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____2782 = (FStar_Util.must (mk_width m))
in TInt (uu____2782))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____2786 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2786 = "FStar.Buffer.buffer")) -> begin
(

let uu____2787 = (translate_type env arg)
in TBuf (uu____2787))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____2788)::[], p) when (

let uu____2791 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2791 = "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when (((ns = ("Prims")::[]) || (ns = ("FStar")::("Pervasives")::("Native")::[])) && (FStar_Util.starts_with t1 "tuple")) -> begin
(

let uu____2813 = (FStar_List.map (translate_type env) args)
in TTuple (uu____2813))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2822 = (

let uu____2829 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____2829)))
in TApp (uu____2822))
end
| uu____2832 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____2835 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____2835))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____2845 -> (match (uu____2845) with
| ((name, uu____2849), typ) -> begin
(

let uu____2853 = (translate_type env typ)
in {name = name; typ = uu____2853; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____2858) -> begin
(

let uu____2859 = (find env name)
in EBound (uu____2859))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____2863 = (

let uu____2866 = (FStar_Util.must (mk_op op))
in (

let uu____2867 = (FStar_Util.must (mk_width m))
in ((uu____2866), (uu____2867))))
in EOp (uu____2863))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____2870 = (

let uu____2873 = (FStar_Util.must (mk_bool_op op))
in ((uu____2873), (Bool)))
in EOp (uu____2870))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n1) -> begin
EQualified (n1)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2878); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print7})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun uu___124_2894 -> (match (uu___124_2894) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| uu____2895 -> begin
false
end)) flags)
in (

let uu____2896 = (match (is_mut) with
| true -> begin
(

let uu____2901 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when (

let uu____2905 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2905 = "FStar.ST.stackref")) -> begin
t
end
| uu____2906 -> begin
(

let uu____2907 = (

let uu____2908 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" uu____2908))
in (failwith uu____2907))
end)
in (

let uu____2910 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (uu____2911, (body1)::[]); FStar_Extraction_ML_Syntax.mlty = uu____2913; FStar_Extraction_ML_Syntax.loc = uu____2914} -> begin
body1
end
| uu____2916 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((uu____2901), (uu____2910))))
end
| uu____2917 -> begin
((typ), (body))
end)
in (match (uu____2896) with
| (typ1, body1) -> begin
(

let binder = (

let uu____2921 = (translate_type env typ1)
in {name = name; typ = uu____2921; mut = is_mut})
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

let uu____2937 = (

let uu____2943 = (translate_expr env expr)
in (

let uu____2944 = (translate_branches env branches)
in ((uu____2943), (uu____2944))))
in EMatch (uu____2937))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2952; FStar_Extraction_ML_Syntax.loc = uu____2953}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v1, uu____2955); FStar_Extraction_ML_Syntax.mlty = uu____2956; FStar_Extraction_ML_Syntax.loc = uu____2957})::[]) when ((

let uu____2959 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2959 = "FStar.HyperStack.ST.op_Bang")) && (is_mutable env v1)) -> begin
(

let uu____2960 = (find env v1)
in EBound (uu____2960))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2962; FStar_Extraction_ML_Syntax.loc = uu____2963}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v1, uu____2965); FStar_Extraction_ML_Syntax.mlty = uu____2966; FStar_Extraction_ML_Syntax.loc = uu____2967})::(e1)::[]) when ((

let uu____2970 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2970 = "FStar.HyperStack.ST.op_Colon_Equals")) && (is_mutable env v1)) -> begin
(

let uu____2971 = (

let uu____2974 = (

let uu____2975 = (find env v1)
in EBound (uu____2975))
in (

let uu____2976 = (translate_expr env e1)
in ((uu____2974), (uu____2976))))
in EAssign (uu____2971))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2978; FStar_Extraction_ML_Syntax.loc = uu____2979}, (e1)::(e2)::[]) when ((

let uu____2983 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2983 = "FStar.Buffer.index")) || (

let uu____2984 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2984 = "FStar.Buffer.op_Array_Access"))) -> begin
(

let uu____2985 = (

let uu____2988 = (translate_expr env e1)
in (

let uu____2989 = (translate_expr env e2)
in ((uu____2988), (uu____2989))))
in EBufRead (uu____2985))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2991; FStar_Extraction_ML_Syntax.loc = uu____2992}, (e1)::(e2)::[]) when (

let uu____2996 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____2996 = "FStar.Buffer.create")) -> begin
(

let uu____2997 = (

let uu____3001 = (translate_expr env e1)
in (

let uu____3002 = (translate_expr env e2)
in ((Stack), (uu____3001), (uu____3002))))
in EBufCreate (uu____2997))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3004; FStar_Extraction_ML_Syntax.loc = uu____3005}, (_e0)::(e1)::(e2)::[]) when (

let uu____3010 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3010 = "FStar.Buffer.rcreate")) -> begin
(

let uu____3011 = (

let uu____3015 = (translate_expr env e1)
in (

let uu____3016 = (translate_expr env e2)
in ((Eternal), (uu____3015), (uu____3016))))
in EBufCreate (uu____3011))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3018; FStar_Extraction_ML_Syntax.loc = uu____3019}, (e2)::[]) when (

let uu____3022 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3022 = "FStar.Buffer.createL")) -> begin
(

let rec list_elements1 = (fun acc e21 -> (match (e21.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd1)::(tl1)::[]) -> begin
(list_elements1 ((hd1)::acc) tl1)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| uu____3046 -> begin
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements2 = (list_elements1 [])
in (

let uu____3052 = (

let uu____3056 = (

let uu____3058 = (list_elements2 e2)
in (FStar_List.map (translate_expr env) uu____3058))
in ((Stack), (uu____3056)))
in EBufCreateL (uu____3052))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3062; FStar_Extraction_ML_Syntax.loc = uu____3063}, (e1)::(e2)::(_e3)::[]) when (

let uu____3068 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3068 = "FStar.Buffer.sub")) -> begin
(

let uu____3069 = (

let uu____3072 = (translate_expr env e1)
in (

let uu____3073 = (translate_expr env e2)
in ((uu____3072), (uu____3073))))
in EBufSub (uu____3069))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3075; FStar_Extraction_ML_Syntax.loc = uu____3076}, (e1)::(e2)::[]) when (

let uu____3080 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3080 = "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3082; FStar_Extraction_ML_Syntax.loc = uu____3083}, (e1)::(e2)::[]) when (

let uu____3087 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3087 = "FStar.Buffer.offset")) -> begin
(

let uu____3088 = (

let uu____3091 = (translate_expr env e1)
in (

let uu____3092 = (translate_expr env e2)
in ((uu____3091), (uu____3092))))
in EBufSub (uu____3088))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3094; FStar_Extraction_ML_Syntax.loc = uu____3095}, (e1)::(e2)::(e3)::[]) when ((

let uu____3100 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3100 = "FStar.Buffer.upd")) || (

let uu____3101 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3101 = "FStar.Buffer.op_Array_Assignment"))) -> begin
(

let uu____3102 = (

let uu____3106 = (translate_expr env e1)
in (

let uu____3107 = (translate_expr env e2)
in (

let uu____3108 = (translate_expr env e3)
in ((uu____3106), (uu____3107), (uu____3108)))))
in EBufWrite (uu____3102))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3110; FStar_Extraction_ML_Syntax.loc = uu____3111}, (uu____3112)::[]) when (

let uu____3114 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3114 = "FStar.HyperStack.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3116; FStar_Extraction_ML_Syntax.loc = uu____3117}, (uu____3118)::[]) when (

let uu____3120 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3120 = "FStar.HyperStack.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3122; FStar_Extraction_ML_Syntax.loc = uu____3123}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (

let uu____3130 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3130 = "FStar.Buffer.blit")) -> begin
(

let uu____3131 = (

let uu____3137 = (translate_expr env e1)
in (

let uu____3138 = (translate_expr env e2)
in (

let uu____3139 = (translate_expr env e3)
in (

let uu____3140 = (translate_expr env e4)
in (

let uu____3141 = (translate_expr env e5)
in ((uu____3137), (uu____3138), (uu____3139), (uu____3140), (uu____3141)))))))
in EBufBlit (uu____3131))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3143; FStar_Extraction_ML_Syntax.loc = uu____3144}, (e1)::(e2)::(e3)::[]) when (

let uu____3149 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3149 = "FStar.Buffer.fill")) -> begin
(

let uu____3150 = (

let uu____3154 = (translate_expr env e1)
in (

let uu____3155 = (translate_expr env e2)
in (

let uu____3156 = (translate_expr env e3)
in ((uu____3154), (uu____3155), (uu____3156)))))
in EBufFill (uu____3150))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3158; FStar_Extraction_ML_Syntax.loc = uu____3159}, (uu____3160)::[]) when (

let uu____3162 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3162 = "FStar.HyperStack.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____3164; FStar_Extraction_ML_Syntax.loc = uu____3165}, (e1)::[]) when (

let uu____3168 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____3168 = "Obj.repr")) -> begin
(

let uu____3169 = (

let uu____3172 = (translate_expr env e1)
in ((uu____3172), (TAny)))
in ECast (uu____3169))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____3175; FStar_Extraction_ML_Syntax.loc = uu____3176}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____3181 = (FStar_Util.must (mk_width m))
in (

let uu____3182 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____3181 uu____3182 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____3184; FStar_Extraction_ML_Syntax.loc = uu____3185}, args) when (is_bool_op op) -> begin
(

let uu____3190 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____3190 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____3192; FStar_Extraction_ML_Syntax.loc = uu____3193}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____3195; FStar_Extraction_ML_Syntax.loc = uu____3196})::[]) when (is_machine_int m) -> begin
(

let uu____3204 = (

let uu____3207 = (FStar_Util.must (mk_width m))
in ((uu____3207), (c)))
in EConstant (uu____3204))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____3209; FStar_Extraction_ML_Syntax.loc = uu____3210}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____3212; FStar_Extraction_ML_Syntax.loc = uu____3213})::[]) when (is_machine_int m) -> begin
(

let uu____3221 = (

let uu____3224 = (FStar_Util.must (mk_width m))
in ((uu____3224), (c)))
in EConstant (uu____3221))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____3225; FStar_Extraction_ML_Syntax.loc = uu____3226}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____3228; FStar_Extraction_ML_Syntax.loc = uu____3229})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____3233 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____3235; FStar_Extraction_ML_Syntax.loc = uu____3236}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____3241 = (

let uu____3244 = (translate_expr env arg)
in ((uu____3244), (TInt (UInt64))))
in ECast (uu____3241))
end
| uu____3245 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____3246 = (

let uu____3249 = (translate_expr env arg)
in ((uu____3249), (TInt (UInt32))))
in ECast (uu____3246))
end
| uu____3250 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____3251 = (

let uu____3254 = (translate_expr env arg)
in ((uu____3254), (TInt (UInt16))))
in ECast (uu____3251))
end
| uu____3255 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____3256 = (

let uu____3259 = (translate_expr env arg)
in ((uu____3259), (TInt (UInt8))))
in ECast (uu____3256))
end
| uu____3260 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____3261 = (

let uu____3264 = (translate_expr env arg)
in ((uu____3264), (TInt (Int64))))
in ECast (uu____3261))
end
| uu____3265 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____3266 = (

let uu____3269 = (translate_expr env arg)
in ((uu____3269), (TInt (Int32))))
in ECast (uu____3266))
end
| uu____3270 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____3271 = (

let uu____3274 = (translate_expr env arg)
in ((uu____3274), (TInt (Int16))))
in ECast (uu____3271))
end
| uu____3275 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____3276 = (

let uu____3279 = (translate_expr env arg)
in ((uu____3279), (TInt (Int8))))
in ECast (uu____3276))
end
| uu____3280 -> begin
(

let uu____3281 = (

let uu____3285 = (

let uu____3287 = (translate_expr env arg)
in (uu____3287)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____3285)))
in EApp (uu____3281))
end)
end)
end)
end)
end)
end)
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = uu____3292; FStar_Extraction_ML_Syntax.loc = uu____3293}, args) -> begin
(

let uu____3299 = (

let uu____3303 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (uu____3303)))
in EApp (uu____3299))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (name, uu____3308); FStar_Extraction_ML_Syntax.mlty = uu____3309; FStar_Extraction_ML_Syntax.loc = uu____3310}, args) -> begin
(

let uu____3314 = (

let uu____3318 = (

let uu____3319 = (find env name)
in EBound (uu____3319))
in (

let uu____3320 = (FStar_List.map (translate_expr env) args)
in ((uu____3318), (uu____3320))))
in EApp (uu____3314))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) -> begin
(

let uu____3326 = (

let uu____3329 = (translate_expr env e1)
in (

let uu____3330 = (translate_type env t_to)
in ((uu____3329), (uu____3330))))
in ECast (uu____3326))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____3331, fields) -> begin
(

let uu____3341 = (

let uu____3347 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3348 = (FStar_List.map (fun uu____3356 -> (match (uu____3356) with
| (field, expr) -> begin
(

let uu____3363 = (translate_expr env expr)
in ((field), (uu____3363)))
end)) fields)
in ((uu____3347), (uu____3348))))
in EFlat (uu____3341))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) -> begin
(

let uu____3369 = (

let uu____3373 = (assert_lid env e1.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3374 = (translate_expr env e1)
in ((uu____3373), (uu____3374), ((FStar_Pervasives_Native.snd path)))))
in EField (uu____3369))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____3376) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, uu____3384) -> begin
(

let uu____3387 = (

let uu____3388 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head1)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____3388))
in (failwith uu____3387))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____3392 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____3392))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____3396 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____3396))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3398, cons1), es) -> begin
(

let uu____3408 = (

let uu____3413 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____3414 = (FStar_List.map (translate_expr env) es)
in ((uu____3413), (cons1), (uu____3414))))
in ECons (uu____3408))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env1 = (add_binders env args)
in (

let uu____3428 = (

let uu____3432 = (translate_expr env1 body)
in ((binders), (uu____3432)))
in EFun (uu____3428))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____3439 = (

let uu____3443 = (translate_expr env e1)
in (

let uu____3444 = (translate_expr env e2)
in (

let uu____3445 = (match (e3) with
| FStar_Pervasives_Native.None -> begin
EUnit
end
| FStar_Pervasives_Native.Some (e31) -> begin
(translate_expr env e31)
end)
in ((uu____3443), (uu____3444), (uu____3445)))))
in EIfThenElse (uu____3439))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____3447) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____3451) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____3459) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3472 = (

let uu____3479 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____3479)))
in TApp (uu____3472))
end
| uu____3482 -> begin
TQualified (lid)
end)
end
| uu____3483 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____3498 -> (match (uu____3498) with
| (pat, guard, expr) -> begin
(match ((guard = FStar_Pervasives_Native.None)) with
| true -> begin
(

let uu____3513 = (translate_pat env pat)
in (match (uu____3513) with
| (env1, pat1) -> begin
(

let uu____3520 = (translate_expr env1 expr)
in ((pat1), (uu____3520)))
end))
end
| uu____3521 -> begin
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____3530) -> begin
(

let env1 = (extend env name false)
in ((env1), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env1 = (extend env "_" false)
in ((env1), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3533, cons1), ps) -> begin
(

let uu____3543 = (FStar_List.fold_left (fun uu____3550 p1 -> (match (uu____3550) with
| (env1, acc) -> begin
(

let uu____3562 = (translate_pat env1 p1)
in (match (uu____3562) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3543) with
| (env1, ps1) -> begin
((env1), (PCons (((cons1), ((FStar_List.rev ps1))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____3579, ps) -> begin
(

let uu____3589 = (FStar_List.fold_left (fun uu____3602 uu____3603 -> (match (((uu____3602), (uu____3603))) with
| ((env1, acc), (field, p1)) -> begin
(

let uu____3640 = (translate_pat env1 p1)
in (match (uu____3640) with
| (env2, p2) -> begin
((env2), ((((field), (p2)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3589) with
| (env1, ps1) -> begin
((env1), (PRecord ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____3674 = (FStar_List.fold_left (fun uu____3681 p1 -> (match (uu____3681) with
| (env1, acc) -> begin
(

let uu____3693 = (translate_pat env1 p1)
in (match (uu____3693) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____3674) with
| (env1, ps1) -> begin
((env1), (PTuple ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____3709) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____3712) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____3719)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____3727) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____3728) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (uu____3729) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____3730) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (uu____3732, FStar_Pervasives_Native.None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____3743 = (

let uu____3747 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____3747)))
in EApp (uu____3743)))




