
open Prims
open FStar_Pervasives
type decl =
| DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int * typ * expr)
| DFunction of (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ * (Prims.string Prims.list * Prims.string) * binder Prims.list * expr)
| DTypeAlias of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * typ)
| DTypeFlat of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list)
| DExternal of (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string Prims.list * Prims.string) * typ)
| DTypeVariant of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list)
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
| TBound of Prims.int
| TApp of ((Prims.string Prims.list * Prims.string) * typ Prims.list)
| TTuple of typ Prims.list


let uu___is_DGlobal : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DGlobal (_0) -> begin
true
end
| uu____696 -> begin
false
end))


let __proj__DGlobal__item___0 : decl  ->  (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int * typ * expr) = (fun projectee -> (match (projectee) with
| DGlobal (_0) -> begin
_0
end))


let uu___is_DFunction : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DFunction (_0) -> begin
true
end
| uu____808 -> begin
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
| uu____934 -> begin
false
end))


let __proj__DTypeAlias__item___0 : decl  ->  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * typ) = (fun projectee -> (match (projectee) with
| DTypeAlias (_0) -> begin
_0
end))


let uu___is_DTypeFlat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeFlat (_0) -> begin
true
end
| uu____1042 -> begin
false
end))


let __proj__DTypeFlat__item___0 : decl  ->  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list) = (fun projectee -> (match (projectee) with
| DTypeFlat (_0) -> begin
_0
end))


let uu___is_DExternal : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DExternal (_0) -> begin
true
end
| uu____1175 -> begin
false
end))


let __proj__DExternal__item___0 : decl  ->  (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string Prims.list * Prims.string) * typ) = (fun projectee -> (match (projectee) with
| DExternal (_0) -> begin
_0
end))


let uu___is_DTypeVariant : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeVariant (_0) -> begin
true
end
| uu____1293 -> begin
false
end))


let __proj__DTypeVariant__item___0 : decl  ->  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list) = (fun projectee -> (match (projectee) with
| DTypeVariant (_0) -> begin
_0
end))


let uu___is_DTypeAbstractStruct : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeAbstractStruct (_0) -> begin
true
end
| uu____1435 -> begin
false
end))


let __proj__DTypeAbstractStruct__item___0 : decl  ->  (Prims.string Prims.list * Prims.string) = (fun projectee -> (match (projectee) with
| DTypeAbstractStruct (_0) -> begin
_0
end))


let uu___is_StdCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| StdCall -> begin
true
end
| uu____1478 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____1489 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____1500 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1511 -> begin
false
end))


let uu___is_WipeBody : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WipeBody -> begin
true
end
| uu____1522 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1533 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1544 -> begin
false
end))


let uu___is_GCType : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GCType -> begin
true
end
| uu____1555 -> begin
false
end))


let uu___is_Comment : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____1568 -> begin
false
end))


let __proj__Comment__item___0 : flag  ->  Prims.string = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
_0
end))


let uu___is_MustDisappear : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MustDisappear -> begin
true
end
| uu____1590 -> begin
false
end))


let uu___is_Const : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____1603 -> begin
false
end))


let __proj__Const__item___0 : flag  ->  Prims.string = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
_0
end))


let uu___is_Prologue : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Prologue (_0) -> begin
true
end
| uu____1627 -> begin
false
end))


let __proj__Prologue__item___0 : flag  ->  Prims.string = (fun projectee -> (match (projectee) with
| Prologue (_0) -> begin
_0
end))


let uu___is_Epilogue : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Epilogue (_0) -> begin
true
end
| uu____1651 -> begin
false
end))


let __proj__Epilogue__item___0 : flag  ->  Prims.string = (fun projectee -> (match (projectee) with
| Epilogue (_0) -> begin
_0
end))


let uu___is_Abstract : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abstract -> begin
true
end
| uu____1673 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____1684 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____1695 -> begin
false
end))


let uu___is_ManuallyManaged : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ManuallyManaged -> begin
true
end
| uu____1706 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____1719 -> begin
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
| uu____1750 -> begin
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
| uu____1799 -> begin
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
| uu____1833 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____1851 -> begin
false
end))


let __proj__EApp__item___0 : expr  ->  (expr * expr Prims.list) = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
_0
end))


let uu___is_ETypApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ETypApp (_0) -> begin
true
end
| uu____1895 -> begin
false
end))


let __proj__ETypApp__item___0 : expr  ->  (expr * typ Prims.list) = (fun projectee -> (match (projectee) with
| ETypApp (_0) -> begin
_0
end))


let uu___is_ELet : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ELet (_0) -> begin
true
end
| uu____1939 -> begin
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
| uu____1983 -> begin
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
| uu____2023 -> begin
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
| uu____2053 -> begin
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
| uu____2091 -> begin
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
| uu____2133 -> begin
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
| uu____2171 -> begin
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
| uu____2213 -> begin
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
| uu____2255 -> begin
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
| uu____2315 -> begin
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
| uu____2369 -> begin
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
| uu____2405 -> begin
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
| uu____2436 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____2447 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____2460 -> begin
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
| uu____2482 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____2493 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____2505 -> begin
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
| uu____2536 -> begin
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
| uu____2596 -> begin
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
| uu____2641 -> begin
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
| uu____2679 -> begin
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
| uu____2719 -> begin
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
| uu____2754 -> begin
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
| uu____2807 -> begin
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
| uu____2846 -> begin
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
| uu____2877 -> begin
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
| uu____2922 -> begin
false
end))


let __proj__EAbortS__item___0 : expr  ->  Prims.string = (fun projectee -> (match (projectee) with
| EAbortS (_0) -> begin
_0
end))


let uu___is_EBufFree : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufFree (_0) -> begin
true
end
| uu____2945 -> begin
false
end))


let __proj__EBufFree__item___0 : expr  ->  expr = (fun projectee -> (match (projectee) with
| EBufFree (_0) -> begin
_0
end))


let uu___is_EBufCreateNoInit : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufCreateNoInit (_0) -> begin
true
end
| uu____2969 -> begin
false
end))


let __proj__EBufCreateNoInit__item___0 : expr  ->  (lifetime * expr) = (fun projectee -> (match (projectee) with
| EBufCreateNoInit (_0) -> begin
_0
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____3000 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____3011 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____3022 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____3033 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____3044 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____3055 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____3066 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____3077 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____3088 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____3099 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____3110 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____3121 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____3132 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____3143 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____3154 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____3165 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____3176 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____3187 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____3198 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____3209 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____3220 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____3231 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____3242 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____3253 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____3264 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____3275 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____3288 -> begin
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
| uu____3311 -> begin
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
| uu____3338 -> begin
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
| uu____3381 -> begin
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
| uu____3414 -> begin
false
end))


let __proj__PRecord__item___0 : pattern  ->  (Prims.string * pattern) Prims.list = (fun projectee -> (match (projectee) with
| PRecord (_0) -> begin
_0
end))


let uu___is_PConstant : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PConstant (_0) -> begin
true
end
| uu____3460 -> begin
false
end))


let __proj__PConstant__item___0 : pattern  ->  (width * Prims.string) = (fun projectee -> (match (projectee) with
| PConstant (_0) -> begin
_0
end))


let uu___is_UInt8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt8 -> begin
true
end
| uu____3494 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____3505 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____3516 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____3527 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____3538 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____3549 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____3560 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____3571 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____3582 -> begin
false
end))


let uu___is_CInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInt -> begin
true
end
| uu____3593 -> begin
false
end))


let __proj__Mkbinder__item__name : binder  ->  Prims.string = (fun projectee -> (match (projectee) with
| {name = name; typ = typ; mut = mut} -> begin
name
end))


let __proj__Mkbinder__item__typ : binder  ->  typ = (fun projectee -> (match (projectee) with
| {name = name; typ = typ; mut = mut} -> begin
typ
end))


let __proj__Mkbinder__item__mut : binder  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = name; typ = typ; mut = mut} -> begin
mut
end))


let uu___is_TInt : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TInt (_0) -> begin
true
end
| uu____3642 -> begin
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
| uu____3662 -> begin
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
| uu____3681 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____3701 -> begin
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
| uu____3744 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____3755 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____3771 -> begin
false
end))


let __proj__TArrow__item___0 : typ  ->  (typ * typ) = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
_0
end))


let uu___is_TBound : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
true
end
| uu____3804 -> begin
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
| uu____3841 -> begin
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
| uu____3905 -> begin
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


type fsdoc =
Prims.string


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


let current_version : version = (Prims.parse_int "27")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 : 'Auu____4008 'Auu____4009 'Auu____4010 . ('Auu____4008 * 'Auu____4009 * 'Auu____4010)  ->  'Auu____4008 = (fun uu____4021 -> (match (uu____4021) with
| (x, uu____4029, uu____4030) -> begin
x
end))


let snd3 : 'Auu____4040 'Auu____4041 'Auu____4042 . ('Auu____4040 * 'Auu____4041 * 'Auu____4042)  ->  'Auu____4041 = (fun uu____4053 -> (match (uu____4053) with
| (uu____4060, x, uu____4062) -> begin
x
end))


let thd3 : 'Auu____4072 'Auu____4073 'Auu____4074 . ('Auu____4072 * 'Auu____4073 * 'Auu____4074)  ->  'Auu____4074 = (fun uu____4085 -> (match (uu____4085) with
| (uu____4092, uu____4093, x) -> begin
x
end))


let mk_width : Prims.string  ->  width FStar_Pervasives_Native.option = (fun uu___283_4103 -> (match (uu___283_4103) with
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
| uu____4115 -> begin
FStar_Pervasives_Native.None
end))


let mk_bool_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___284_4125 -> (match (uu___284_4125) with
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
| uu____4134 -> begin
FStar_Pervasives_Native.None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> (Prims.op_disEquality (mk_bool_op op) FStar_Pervasives_Native.None))


let mk_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___285_4155 -> (match (uu___285_4155) with
| "add" -> begin
FStar_Pervasives_Native.Some (Add)
end
| "op_Plus_Hat" -> begin
FStar_Pervasives_Native.Some (Add)
end
| "add_underspec" -> begin
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
| "sub_underspec" -> begin
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
| uu____4200 -> begin
FStar_Pervasives_Native.None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> (Prims.op_disEquality (mk_op op) FStar_Pervasives_Native.None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> (Prims.op_disEquality (mk_width m) FStar_Pervasives_Native.None))

type env =
{names : name Prims.list; names_t : Prims.string Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string}


let __proj__Mkenv__item__names : env  ->  name Prims.list = (fun projectee -> (match (projectee) with
| {names = names; names_t = names_t; module_name = module_name} -> begin
names
end))


let __proj__Mkenv__item__names_t : env  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {names = names; names_t = names_t; module_name = module_name} -> begin
names_t
end))


let __proj__Mkenv__item__module_name : env  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {names = names; names_t = names_t; module_name = module_name} -> begin
module_name
end))


let __proj__Mkname__item__pretty : name  ->  Prims.string = (fun projectee -> (match (projectee) with
| {pretty = pretty1} -> begin
pretty1
end))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; names_t = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___291_4356 = env
in {names = ({pretty = x})::env.names; names_t = uu___291_4356.names_t; module_name = uu___291_4356.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___292_4370 = env
in {names = uu___292_4370.names; names_t = (x)::env.names_t; module_name = uu___292_4370.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____4385 = (FStar_List.tryFind (fun name -> (Prims.op_Equality name.pretty x)) env.names)
in (match (uu____4385) with
| FStar_Pervasives_Native.Some (name) -> begin
name
end
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: name not found")
end)))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_All.try_with (fun uu___294_4409 -> (match (()) with
| () -> begin
(FStar_List.index (fun name -> (Prims.op_Equality name.pretty x)) env.names)
end)) (fun uu___293_4416 -> (

let uu____4418 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____4418)))))


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_All.try_with (fun uu___296_4438 -> (match (()) with
| () -> begin
(FStar_List.index (fun name -> (Prims.op_Equality name x)) env.names_t)
end)) (fun uu___295_4447 -> (

let uu____4449 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____4449)))))


let add_binders : 'Auu____4460 . env  ->  (Prims.string * 'Auu____4460) Prims.list  ->  env = (fun env binders -> (FStar_List.fold_left (fun env1 uu____4495 -> (match (uu____4495) with
| (name, uu____4502) -> begin
(extend env1 name)
end)) env binders))


let list_elements : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list = (fun e2 -> (

let rec list_elements = (fun acc e21 -> (match (e21.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd1)::(tl1)::[]) -> begin
(list_elements ((hd1)::acc) tl1)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| uu____4554 -> begin
(failwith "Argument of FStar.Buffer.createL is not a list literal!")
end))
in (list_elements [] e2)))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____4773 -> (match (uu____4773) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____4822 = m
in (match (uu____4822) with
| (path, uu____4837, uu____4838) -> begin
(FStar_Extraction_ML_Syntax.string_of_mlpath path)
end))
in (FStar_All.try_with (fun uu___298_4856 -> (match (()) with
| () -> begin
((

let uu____4860 = (

let uu____4862 = (FStar_Options.silent ())
in (not (uu____4862)))
in (match (uu____4860) with
| true -> begin
(FStar_Util.print1 "Attempting to translate module %s\n" m_name)
end
| uu____4866 -> begin
()
end));
(

let uu____4868 = (translate_module m)
in FStar_Pervasives_Native.Some (uu____4868));
)
end)) (fun uu___297_4872 -> (match (uu___297_4872) with
| e -> begin
((

let uu____4877 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____4877));
FStar_Pervasives_Native.None;
)
end))))) modules)
end))
and translate_module : (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____4880 -> (match (uu____4880) with
| (module_name, modul, uu____4895) -> begin
(

let module_name1 = (FStar_List.append (FStar_Pervasives_Native.fst module_name) (((FStar_Pervasives_Native.snd module_name))::[]))
in (

let program = (match (modul) with
| FStar_Pervasives_Native.Some (_signature, decls) -> begin
(FStar_List.collect (translate_decl (empty module_name1)) decls)
end
| uu____4930 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name1)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.meta Prims.list  ->  flag Prims.list = (fun flags1 -> (FStar_List.choose (fun uu___286_4944 -> (match (uu___286_4944) with
| FStar_Extraction_ML_Syntax.Private -> begin
FStar_Pervasives_Native.Some (Private)
end
| FStar_Extraction_ML_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (WipeBody)
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
| FStar_Extraction_ML_Syntax.Comment (s) -> begin
FStar_Pervasives_Native.Some (Comment (s))
end
| FStar_Extraction_ML_Syntax.StackInline -> begin
FStar_Pervasives_Native.Some (MustDisappear)
end
| FStar_Extraction_ML_Syntax.CConst (s) -> begin
FStar_Pervasives_Native.Some (Const (s))
end
| FStar_Extraction_ML_Syntax.CPrologue (s) -> begin
FStar_Pervasives_Native.Some (Prologue (s))
end
| FStar_Extraction_ML_Syntax.CEpilogue (s) -> begin
FStar_Pervasives_Native.Some (Epilogue (s))
end
| FStar_Extraction_ML_Syntax.CAbstract -> begin
FStar_Pervasives_Native.Some (Abstract)
end
| uu____4955 -> begin
FStar_Pervasives_Native.None
end)) flags1))
and translate_cc : FStar_Extraction_ML_Syntax.meta Prims.list  ->  cc FStar_Pervasives_Native.option = (fun flags1 -> (

let uu____4959 = (FStar_List.choose (fun uu___287_4966 -> (match (uu___287_4966) with
| FStar_Extraction_ML_Syntax.CCConv (s) -> begin
FStar_Pervasives_Native.Some (s)
end
| uu____4973 -> begin
FStar_Pervasives_Native.None
end)) flags1)
in (match (uu____4959) with
| ("stdcall")::[] -> begin
FStar_Pervasives_Native.Some (StdCall)
end
| ("fastcall")::[] -> begin
FStar_Pervasives_Native.Some (FastCall)
end
| ("cdecl")::[] -> begin
FStar_Pervasives_Native.Some (CDecl)
end
| uu____4986 -> begin
FStar_Pervasives_Native.None
end)))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.list = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) -> begin
(FStar_List.choose (translate_let env flavor) lbs)
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____5000) -> begin
[]
end
| FStar_Extraction_ML_Syntax.MLM_Ty (tys) -> begin
(FStar_List.choose (translate_type_decl env) tys)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____5002) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____5007) -> begin
((FStar_Util.print1_warning "Not extracting exception %s to KreMLin (exceptions unsupported)\n" m);
[];
)
end))
and translate_let : env  ->  FStar_Extraction_ML_Syntax.mlletflavor  ->  FStar_Extraction_ML_Syntax.mllb  ->  decl FStar_Pervasives_Native.option = (fun env flavor lb -> (match (lb) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5034; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____5037} when (FStar_Util.for_some (fun uu___288_5042 -> (match (uu___288_5042) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____5045 -> begin
false
end)) meta) -> begin
(

let name1 = ((env.module_name), (name))
in (match ((Prims.op_Equality (FStar_List.length tvars) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5066 = (

let uu____5067 = (

let uu____5088 = (translate_cc meta)
in (

let uu____5091 = (translate_flags meta)
in (

let uu____5094 = (translate_type env t0)
in ((uu____5088), (uu____5091), (name1), (uu____5094)))))
in DExternal (uu____5067))
in FStar_Pervasives_Native.Some (uu____5066))
end
| uu____5107 -> begin
((

let uu____5110 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print1_warning "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n" uu____5110));
FStar_Pervasives_Native.None;
)
end))
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5116; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____5119; FStar_Extraction_ML_Syntax.loc = uu____5120}; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____5122} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5143 -> begin
(

let env1 = (match ((Prims.op_Equality flavor FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name)
end
| uu____5147 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 name1 -> (extend_t env2 name1)) env1 tvars)
in (

let rec find_return_type = (fun eff i uu___289_5179 -> (match (uu___289_5179) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5188, eff1, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type eff1 (i - (Prims.parse_int "1")) t)
end
| t -> begin
((i), (eff), (t))
end))
in (

let name1 = ((env2.module_name), (name))
in (

let uu____5208 = (find_return_type FStar_Extraction_ML_Syntax.E_PURE (FStar_List.length args) t0)
in (match (uu____5208) with
| (i, eff, t) -> begin
((match ((i > (Prims.parse_int "0"))) with
| true -> begin
(

let msg = "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
in (

let uu____5234 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print2_warning "Not extracting %s to KreMLin (%s)\n" uu____5234 msg)))
end
| uu____5237 -> begin
()
end);
(

let t1 = (translate_type env2 t)
in (

let binders = (translate_binders env2 args)
in (

let env3 = (add_binders env2 args)
in (

let cc = (translate_cc meta)
in (

let meta1 = (match (((eff), (t1))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____5252) -> begin
(

let uu____5253 = (translate_flags meta)
in (MustDisappear)::uu____5253)
end
| (FStar_Extraction_ML_Syntax.E_PURE, TUnit) -> begin
(

let uu____5256 = (translate_flags meta)
in (MustDisappear)::uu____5256)
end
| uu____5259 -> begin
(translate_flags meta)
end)
in (FStar_All.try_with (fun uu___300_5268 -> (match (()) with
| () -> begin
(

let body1 = (translate_expr env3 body)
in FStar_Pervasives_Native.Some (DFunction (((cc), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (body1)))))
end)) (fun uu___299_5293 -> (match (uu___299_5293) with
| e -> begin
(

let msg = (FStar_Util.print_exn e)
in ((

let uu____5300 = (

let uu____5306 = (

let uu____5308 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.format2 "Error while extracting %s to KreMLin (%s)\n" uu____5308 msg))
in ((FStar_Errors.Warning_FunctionNotExtacted), (uu____5306)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____5300));
(

let msg1 = (Prims.strcat "This function was not extracted:\n" msg)
in FStar_Pervasives_Native.Some (DFunction (((cc), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (EAbortS (msg1))))));
))
end))))))));
)
end))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5334; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____5337} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5344 -> begin
(

let meta1 = (translate_flags meta)
in (

let env1 = (FStar_List.fold_left (fun env1 name1 -> (extend_t env1 name1)) env tvars)
in (

let t1 = (translate_type env1 t)
in (

let name1 = ((env1.module_name), (name))
in (FStar_All.try_with (fun uu___302_5374 -> (match (()) with
| () -> begin
(

let expr1 = (translate_expr env1 expr)
in FStar_Pervasives_Native.Some (DGlobal (((meta1), (name1), ((FStar_List.length tvars)), (t1), (expr1)))))
end)) (fun uu___301_5393 -> (match (uu___301_5393) with
| e -> begin
((

let uu____5398 = (

let uu____5404 = (

let uu____5406 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (

let uu____5408 = (FStar_Util.print_exn e)
in (FStar_Util.format2 "Error extracting %s to KreMLin (%s)\n" uu____5406 uu____5408)))
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____5404)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____5398));
FStar_Pervasives_Native.Some (DGlobal (((meta1), (name1), ((FStar_List.length tvars)), (t1), (EAny))));
)
end)))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5426; FStar_Extraction_ML_Syntax.mllb_def = uu____5427; FStar_Extraction_ML_Syntax.mllb_meta = uu____5428; FStar_Extraction_ML_Syntax.print_typ = uu____5429} -> begin
((

let uu____5436 = (

let uu____5442 = (FStar_Util.format1 "Not extracting %s to KreMLin\n" name)
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____5442)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____5436));
(match (ts) with
| FStar_Pervasives_Native.Some (idents, t) -> begin
(

let uu____5449 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" (FStar_String.concat ", " idents) uu____5449))
end
| FStar_Pervasives_Native.None -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
and translate_type_decl : env  ->  FStar_Extraction_ML_Syntax.one_mltydecl  ->  decl FStar_Pervasives_Native.option = (fun env ty -> (

let uu____5463 = ty
in (match (uu____5463) with
| (uu____5466, uu____5467, uu____5468, uu____5469, flags1, uu____5471) -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags1)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5489 -> begin
(match (ty) with
| (assumed, name, _mangled_name, args, flags2, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 name2 -> (extend_t env1 name2)) env args)
in (match ((assumed && (FStar_List.mem FStar_Extraction_ML_Syntax.CAbstract flags2))) with
| true -> begin
FStar_Pervasives_Native.Some (DTypeAbstractStruct (name1))
end
| uu____5534 -> begin
(match (assumed) with
| true -> begin
(

let name2 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in ((FStar_Util.print1_warning "Not extracting type definition %s to KreMLin (assumed type)\n" name2);
FStar_Pervasives_Native.None;
))
end
| uu____5543 -> begin
(

let uu____5545 = (

let uu____5546 = (

let uu____5566 = (translate_flags flags2)
in (

let uu____5569 = (translate_type env1 t)
in ((name1), (uu____5566), ((FStar_List.length args)), (uu____5569))))
in DTypeAlias (uu____5546))
in FStar_Pervasives_Native.Some (uu____5545))
end)
end)))
end
| (uu____5582, name, _mangled_name, args, flags2, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 name2 -> (extend_t env1 name2)) env args)
in (

let uu____5627 = (

let uu____5628 = (

let uu____5660 = (translate_flags flags2)
in (

let uu____5663 = (FStar_List.map (fun uu____5695 -> (match (uu____5695) with
| (f, t) -> begin
(

let uu____5715 = (

let uu____5721 = (translate_type env1 t)
in ((uu____5721), (false)))
in ((f), (uu____5715)))
end)) fields)
in ((name1), (uu____5660), ((FStar_List.length args)), (uu____5663))))
in DTypeFlat (uu____5628))
in FStar_Pervasives_Native.Some (uu____5627))))
end
| (uu____5754, name, _mangled_name, args, flags2, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let flags3 = (translate_flags flags2)
in (

let env1 = (FStar_List.fold_left extend_t env args)
in (

let uu____5804 = (

let uu____5805 = (

let uu____5844 = (FStar_List.map (fun uu____5897 -> (match (uu____5897) with
| (cons1, ts) -> begin
(

let uu____5945 = (FStar_List.map (fun uu____5977 -> (match (uu____5977) with
| (name2, t) -> begin
(

let uu____5997 = (

let uu____6003 = (translate_type env1 t)
in ((uu____6003), (false)))
in ((name2), (uu____5997)))
end)) ts)
in ((cons1), (uu____5945)))
end)) branches)
in ((name1), (flags3), ((FStar_List.length args)), (uu____5844)))
in DTypeVariant (uu____5805))
in FStar_Pervasives_Native.Some (uu____5804)))))
end
| (uu____6056, name, _mangled_name, uu____6059, uu____6060, uu____6061) -> begin
((

let uu____6077 = (

let uu____6083 = (FStar_Util.format1 "Error extracting type definition %s to KreMLin\n" name)
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____6083)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____6077));
FStar_Pervasives_Native.None;
)
end)
end)
end)))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Tuple ([]) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name) -> begin
(

let uu____6091 = (find_t env name)
in TBound (uu____6091))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____6094, t2) -> begin
(

let uu____6096 = (

let uu____6101 = (translate_type env t1)
in (

let uu____6102 = (translate_type env t2)
in ((uu____6101), (uu____6102))))
in TArrow (uu____6096))
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____6106 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6106 "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____6113 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6113 "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____6130 = (FStar_Util.must (mk_width m))
in TInt (uu____6130))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____6144 = (FStar_Util.must (mk_width m))
in TInt (uu____6144))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____6149 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6149 "FStar.Monotonic.HyperStack.mem")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____6153)::(arg)::(uu____6155)::[], p) when ((((

let uu____6161 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6161 "FStar.Monotonic.HyperStack.s_mref")) || (

let uu____6166 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6166 "FStar.Monotonic.HyperHeap.mrref"))) || (

let uu____6171 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6171 "FStar.HyperStack.ST.m_rref"))) || (

let uu____6176 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6176 "FStar.HyperStack.ST.s_mref"))) -> begin
(

let uu____6180 = (translate_type env arg)
in TBuf (uu____6180))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::(uu____6182)::[], p) when (((((((((((

let uu____6188 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6188 "FStar.Monotonic.HyperStack.mreference")) || (

let uu____6193 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6193 "FStar.Monotonic.HyperStack.mstackref"))) || (

let uu____6198 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6198 "FStar.Monotonic.HyperStack.mref"))) || (

let uu____6203 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6203 "FStar.Monotonic.HyperStack.mmmstackref"))) || (

let uu____6208 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6208 "FStar.Monotonic.HyperStack.mmmref"))) || (

let uu____6213 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6213 "FStar.Monotonic.Heap.mref"))) || (

let uu____6218 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6218 "FStar.HyperStack.ST.mreference"))) || (

let uu____6223 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6223 "FStar.HyperStack.ST.mstackref"))) || (

let uu____6228 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6228 "FStar.HyperStack.ST.mref"))) || (

let uu____6233 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6233 "FStar.HyperStack.ST.mmmstackref"))) || (

let uu____6238 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6238 "FStar.HyperStack.ST.mmmref"))) -> begin
(

let uu____6242 = (translate_type env arg)
in TBuf (uu____6242))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::(uu____6244)::(uu____6245)::[], p) when (

let uu____6249 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6249 "LowStar.Monotonic.Buffer.mbuffer")) -> begin
(

let uu____6253 = (translate_type env arg)
in TBuf (uu____6253))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((((((((((((((

let uu____6260 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6260 "FStar.Buffer.buffer")) || (

let uu____6265 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6265 "LowStar.Buffer.buffer"))) || (

let uu____6270 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6270 "LowStar.ImmutableBuffer.ibuffer"))) || (

let uu____6275 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6275 "LowStar.UninitializedBuffer.ubuffer"))) || (

let uu____6280 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6280 "FStar.HyperStack.reference"))) || (

let uu____6285 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6285 "FStar.HyperStack.stackref"))) || (

let uu____6290 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6290 "FStar.HyperStack.ref"))) || (

let uu____6295 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6295 "FStar.HyperStack.mmstackref"))) || (

let uu____6300 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6300 "FStar.HyperStack.mmref"))) || (

let uu____6305 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6305 "FStar.HyperStack.ST.reference"))) || (

let uu____6310 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6310 "FStar.HyperStack.ST.stackref"))) || (

let uu____6315 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6315 "FStar.HyperStack.ST.ref"))) || (

let uu____6320 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6320 "FStar.HyperStack.ST.mmstackref"))) || (

let uu____6325 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6325 "FStar.HyperStack.ST.mmref"))) -> begin
(

let uu____6329 = (translate_type env arg)
in TBuf (uu____6329))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____6330)::(arg)::[], p) when ((

let uu____6337 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6337 "FStar.HyperStack.s_ref")) || (

let uu____6342 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6342 "FStar.HyperStack.ST.s_ref"))) -> begin
(

let uu____6346 = (translate_type env arg)
in TBuf (uu____6346))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____6347)::[], p) when (

let uu____6351 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6351 "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when (((Prims.op_Equality ns (("Prims")::[])) || (Prims.op_Equality ns (("FStar")::("Pervasives")::("Native")::[]))) && (FStar_Util.starts_with t1 "tuple")) -> begin
(

let uu____6403 = (FStar_List.map (translate_type env) args)
in TTuple (uu____6403))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6414 = (

let uu____6429 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____6429)))
in TApp (uu____6414))
end
| uu____6442 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____6447 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____6447))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____6465 -> (match (uu____6465) with
| (name, typ) -> begin
(

let uu____6475 = (translate_type env typ)
in {name = name; typ = uu____6475; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name) -> begin
(

let uu____6482 = (find env name)
in EBound (uu____6482))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____6496 = (

let uu____6501 = (FStar_Util.must (mk_op op))
in (

let uu____6502 = (FStar_Util.must (mk_width m))
in ((uu____6501), (uu____6502))))
in EOp (uu____6496))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____6512 = (

let uu____6517 = (FStar_Util.must (mk_bool_op op))
in ((uu____6517), (Bool)))
in EOp (uu____6512))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n1) -> begin
EQualified (n1)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.mllb_meta = flags1; FStar_Extraction_ML_Syntax.print_typ = print7})::[]), continuation) -> begin
(

let binder = (

let uu____6540 = (translate_type env typ)
in {name = name; typ = uu____6540; mut = false})
in (

let body1 = (translate_expr env body)
in (

let env1 = (extend env name)
in (

let continuation1 = (translate_expr env1 continuation)
in ELet (((binder), (body1), (continuation1)))))))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(

let uu____6567 = (

let uu____6578 = (translate_expr env expr)
in (

let uu____6579 = (translate_branches env branches)
in ((uu____6578), (uu____6579))))
in EMatch (uu____6567))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6593; FStar_Extraction_ML_Syntax.loc = uu____6594}, (t)::[]); FStar_Extraction_ML_Syntax.mlty = uu____6596; FStar_Extraction_ML_Syntax.loc = uu____6597}, (arg)::[]) when (

let uu____6603 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6603 "FStar.Dyn.undyn")) -> begin
(

let uu____6607 = (

let uu____6612 = (translate_expr env arg)
in (

let uu____6613 = (translate_type env t)
in ((uu____6612), (uu____6613))))
in ECast (uu____6607))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6615; FStar_Extraction_ML_Syntax.loc = uu____6616}, uu____6617); FStar_Extraction_ML_Syntax.mlty = uu____6618; FStar_Extraction_ML_Syntax.loc = uu____6619}, uu____6620) when (

let uu____6629 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6629 "Prims.admit")) -> begin
EAbort
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6634; FStar_Extraction_ML_Syntax.loc = uu____6635}, uu____6636); FStar_Extraction_ML_Syntax.mlty = uu____6637; FStar_Extraction_ML_Syntax.loc = uu____6638}, (arg)::[]) when (((

let uu____6648 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6648 "FStar.HyperStack.All.failwith")) || (

let uu____6653 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6653 "FStar.Error.unexpected"))) || (

let uu____6658 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6658 "FStar.Error.unreachable"))) -> begin
(match (arg) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (msg)); FStar_Extraction_ML_Syntax.mlty = uu____6663; FStar_Extraction_ML_Syntax.loc = uu____6664} -> begin
EAbortS (msg)
end
| uu____6666 -> begin
(

let print7 = (

let uu____6668 = (

let uu____6669 = (

let uu____6670 = (FStar_Ident.lid_of_str "FStar.HyperStack.IO.print_string")
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6670))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____6669))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____6668))
in (

let print8 = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top (FStar_Extraction_ML_Syntax.MLE_App (((print7), ((arg)::[])))))
in (

let t = (translate_expr env print8)
in ESequence ((t)::(EAbort)::[]))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6677; FStar_Extraction_ML_Syntax.loc = uu____6678}, uu____6679); FStar_Extraction_ML_Syntax.mlty = uu____6680; FStar_Extraction_ML_Syntax.loc = uu____6681}, (e1)::[]) when ((

let uu____6691 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6691 "LowStar.ToFStarBuffer.new_to_old_st")) || (

let uu____6696 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6696 "LowStar.ToFStarBuffer.old_to_new_st"))) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6701; FStar_Extraction_ML_Syntax.loc = uu____6702}, uu____6703); FStar_Extraction_ML_Syntax.mlty = uu____6704; FStar_Extraction_ML_Syntax.loc = uu____6705}, (e1)::(e2)::[]) when ((((

let uu____6716 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6716 "FStar.Buffer.index")) || (

let uu____6721 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6721 "FStar.Buffer.op_Array_Access"))) || (

let uu____6726 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6726 "LowStar.Monotonic.Buffer.index"))) || (

let uu____6731 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6731 "LowStar.UninitializedBuffer.uindex"))) -> begin
(

let uu____6735 = (

let uu____6740 = (translate_expr env e1)
in (

let uu____6741 = (translate_expr env e2)
in ((uu____6740), (uu____6741))))
in EBufRead (uu____6735))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6743; FStar_Extraction_ML_Syntax.loc = uu____6744}, uu____6745); FStar_Extraction_ML_Syntax.mlty = uu____6746; FStar_Extraction_ML_Syntax.loc = uu____6747}, (e1)::[]) when (

let uu____6755 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6755 "FStar.HyperStack.ST.op_Bang")) -> begin
(

let uu____6759 = (

let uu____6764 = (translate_expr env e1)
in ((uu____6764), (EConstant (((UInt32), ("0"))))))
in EBufRead (uu____6759))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6768; FStar_Extraction_ML_Syntax.loc = uu____6769}, uu____6770); FStar_Extraction_ML_Syntax.mlty = uu____6771; FStar_Extraction_ML_Syntax.loc = uu____6772}, (e1)::(e2)::[]) when (((

let uu____6783 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6783 "FStar.Buffer.create")) || (

let uu____6788 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6788 "LowStar.Monotonic.Buffer.malloca"))) || (

let uu____6793 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6793 "LowStar.ImmutableBuffer.ialloca"))) -> begin
(

let uu____6797 = (

let uu____6804 = (translate_expr env e1)
in (

let uu____6805 = (translate_expr env e2)
in ((Stack), (uu____6804), (uu____6805))))
in EBufCreate (uu____6797))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6807; FStar_Extraction_ML_Syntax.loc = uu____6808}, uu____6809); FStar_Extraction_ML_Syntax.mlty = uu____6810; FStar_Extraction_ML_Syntax.loc = uu____6811}, (elen)::[]) when (

let uu____6819 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6819 "LowStar.UninitializedBuffer.ualloca")) -> begin
(

let uu____6823 = (

let uu____6828 = (translate_expr env elen)
in ((Stack), (uu____6828)))
in EBufCreateNoInit (uu____6823))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6830; FStar_Extraction_ML_Syntax.loc = uu____6831}, uu____6832); FStar_Extraction_ML_Syntax.mlty = uu____6833; FStar_Extraction_ML_Syntax.loc = uu____6834}, (init1)::[]) when (

let uu____6842 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6842 "FStar.HyperStack.ST.salloc")) -> begin
(

let uu____6846 = (

let uu____6853 = (translate_expr env init1)
in ((Stack), (uu____6853), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____6846))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6857; FStar_Extraction_ML_Syntax.loc = uu____6858}, uu____6859); FStar_Extraction_ML_Syntax.mlty = uu____6860; FStar_Extraction_ML_Syntax.loc = uu____6861}, (e2)::[]) when (((

let uu____6871 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6871 "FStar.Buffer.createL")) || (

let uu____6876 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6876 "LowStar.Monotonic.Buffer.malloca_of_list"))) || (

let uu____6881 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6881 "LowStar.ImmutableBuffer.ialloca_of_list"))) -> begin
(

let uu____6885 = (

let uu____6892 = (

let uu____6895 = (list_elements e2)
in (FStar_List.map (translate_expr env) uu____6895))
in ((Stack), (uu____6892)))
in EBufCreateL (uu____6885))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6901; FStar_Extraction_ML_Syntax.loc = uu____6902}, uu____6903); FStar_Extraction_ML_Syntax.mlty = uu____6904; FStar_Extraction_ML_Syntax.loc = uu____6905}, (_erid)::(e2)::[]) when ((

let uu____6916 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6916 "LowStar.Monotonic.Buffer.mgcmalloc_of_list")) || (

let uu____6921 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6921 "LowStar.ImmutableBuffer.igcmalloc_of_list"))) -> begin
(

let uu____6925 = (

let uu____6932 = (

let uu____6935 = (list_elements e2)
in (FStar_List.map (translate_expr env) uu____6935))
in ((Eternal), (uu____6932)))
in EBufCreateL (uu____6925))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6941; FStar_Extraction_ML_Syntax.loc = uu____6942}, uu____6943); FStar_Extraction_ML_Syntax.mlty = uu____6944; FStar_Extraction_ML_Syntax.loc = uu____6945}, (_rid)::(init1)::[]) when (

let uu____6954 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6954 "FStar.HyperStack.ST.ralloc")) -> begin
(

let uu____6958 = (

let uu____6965 = (translate_expr env init1)
in ((Eternal), (uu____6965), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____6958))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6969; FStar_Extraction_ML_Syntax.loc = uu____6970}, uu____6971); FStar_Extraction_ML_Syntax.mlty = uu____6972; FStar_Extraction_ML_Syntax.loc = uu____6973}, (_e0)::(e1)::(e2)::[]) when (((

let uu____6985 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6985 "FStar.Buffer.rcreate")) || (

let uu____6990 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6990 "LowStar.Monotonic.Buffer.mgcmalloc"))) || (

let uu____6995 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6995 "LowStar.ImmutableBuffer.igcmalloc"))) -> begin
(

let uu____6999 = (

let uu____7006 = (translate_expr env e1)
in (

let uu____7007 = (translate_expr env e2)
in ((Eternal), (uu____7006), (uu____7007))))
in EBufCreate (uu____6999))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7009; FStar_Extraction_ML_Syntax.loc = uu____7010}, uu____7011); FStar_Extraction_ML_Syntax.mlty = uu____7012; FStar_Extraction_ML_Syntax.loc = uu____7013}, (_erid)::(elen)::[]) when (

let uu____7022 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7022 "LowStar.UninitializedBuffer.ugcmalloc")) -> begin
(

let uu____7026 = (

let uu____7031 = (translate_expr env elen)
in ((Eternal), (uu____7031)))
in EBufCreateNoInit (uu____7026))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7033; FStar_Extraction_ML_Syntax.loc = uu____7034}, uu____7035); FStar_Extraction_ML_Syntax.mlty = uu____7036; FStar_Extraction_ML_Syntax.loc = uu____7037}, (_rid)::(init1)::[]) when (

let uu____7046 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7046 "FStar.HyperStack.ST.ralloc_mm")) -> begin
(

let uu____7050 = (

let uu____7057 = (translate_expr env init1)
in ((ManuallyManaged), (uu____7057), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____7050))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7061; FStar_Extraction_ML_Syntax.loc = uu____7062}, uu____7063); FStar_Extraction_ML_Syntax.mlty = uu____7064; FStar_Extraction_ML_Syntax.loc = uu____7065}, (_e0)::(e1)::(e2)::[]) when ((((

let uu____7077 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7077 "FStar.Buffer.rcreate_mm")) || (

let uu____7082 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7082 "LowStar.Monotonic.Buffer.mmalloc"))) || (

let uu____7087 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7087 "LowStar.Monotonic.Buffer.mmalloc"))) || (

let uu____7092 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7092 "LowStar.ImmutableBuffer.imalloc"))) -> begin
(

let uu____7096 = (

let uu____7103 = (translate_expr env e1)
in (

let uu____7104 = (translate_expr env e2)
in ((ManuallyManaged), (uu____7103), (uu____7104))))
in EBufCreate (uu____7096))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7106; FStar_Extraction_ML_Syntax.loc = uu____7107}, uu____7108); FStar_Extraction_ML_Syntax.mlty = uu____7109; FStar_Extraction_ML_Syntax.loc = uu____7110}, (_erid)::(elen)::[]) when (

let uu____7119 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7119 "LowStar.UninitializedBuffer.umalloc")) -> begin
(

let uu____7123 = (

let uu____7128 = (translate_expr env elen)
in ((ManuallyManaged), (uu____7128)))
in EBufCreateNoInit (uu____7123))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7130; FStar_Extraction_ML_Syntax.loc = uu____7131}, uu____7132); FStar_Extraction_ML_Syntax.mlty = uu____7133; FStar_Extraction_ML_Syntax.loc = uu____7134}, (e2)::[]) when (

let uu____7142 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7142 "FStar.HyperStack.ST.rfree")) -> begin
(

let uu____7146 = (translate_expr env e2)
in EBufFree (uu____7146))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7148; FStar_Extraction_ML_Syntax.loc = uu____7149}, uu____7150); FStar_Extraction_ML_Syntax.mlty = uu____7151; FStar_Extraction_ML_Syntax.loc = uu____7152}, (e2)::[]) when ((

let uu____7162 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7162 "FStar.Buffer.rfree")) || (

let uu____7167 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7167 "LowStar.Monotonic.Buffer.free"))) -> begin
(

let uu____7171 = (translate_expr env e2)
in EBufFree (uu____7171))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7173; FStar_Extraction_ML_Syntax.loc = uu____7174}, uu____7175); FStar_Extraction_ML_Syntax.mlty = uu____7176; FStar_Extraction_ML_Syntax.loc = uu____7177}, (e1)::(e2)::(_e3)::[]) when (

let uu____7187 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7187 "FStar.Buffer.sub")) -> begin
(

let uu____7191 = (

let uu____7196 = (translate_expr env e1)
in (

let uu____7197 = (translate_expr env e2)
in ((uu____7196), (uu____7197))))
in EBufSub (uu____7191))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7199; FStar_Extraction_ML_Syntax.loc = uu____7200}, uu____7201); FStar_Extraction_ML_Syntax.mlty = uu____7202; FStar_Extraction_ML_Syntax.loc = uu____7203}, (e1)::(e2)::(_e3)::[]) when (

let uu____7213 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7213 "LowStar.Monotonic.Buffer.msub")) -> begin
(

let uu____7217 = (

let uu____7222 = (translate_expr env e1)
in (

let uu____7223 = (translate_expr env e2)
in ((uu____7222), (uu____7223))))
in EBufSub (uu____7217))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7225; FStar_Extraction_ML_Syntax.loc = uu____7226}, uu____7227); FStar_Extraction_ML_Syntax.mlty = uu____7228; FStar_Extraction_ML_Syntax.loc = uu____7229}, (e1)::(e2)::[]) when (

let uu____7238 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7238 "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7243; FStar_Extraction_ML_Syntax.loc = uu____7244}, uu____7245); FStar_Extraction_ML_Syntax.mlty = uu____7246; FStar_Extraction_ML_Syntax.loc = uu____7247}, (e1)::(e2)::[]) when (

let uu____7256 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7256 "FStar.Buffer.offset")) -> begin
(

let uu____7260 = (

let uu____7265 = (translate_expr env e1)
in (

let uu____7266 = (translate_expr env e2)
in ((uu____7265), (uu____7266))))
in EBufSub (uu____7260))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7268; FStar_Extraction_ML_Syntax.loc = uu____7269}, uu____7270); FStar_Extraction_ML_Syntax.mlty = uu____7271; FStar_Extraction_ML_Syntax.loc = uu____7272}, (e1)::(e2)::[]) when (

let uu____7281 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7281 "LowStar.Monotonic.Buffer.moffset")) -> begin
(

let uu____7285 = (

let uu____7290 = (translate_expr env e1)
in (

let uu____7291 = (translate_expr env e2)
in ((uu____7290), (uu____7291))))
in EBufSub (uu____7285))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7293; FStar_Extraction_ML_Syntax.loc = uu____7294}, uu____7295); FStar_Extraction_ML_Syntax.mlty = uu____7296; FStar_Extraction_ML_Syntax.loc = uu____7297}, (e1)::(e2)::(e3)::[]) when ((((

let uu____7309 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7309 "FStar.Buffer.upd")) || (

let uu____7314 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7314 "FStar.Buffer.op_Array_Assignment"))) || (

let uu____7319 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7319 "LowStar.Monotonic.Buffer.upd\'"))) || (

let uu____7324 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7324 "LowStar.UninitializedBuffer.uupd"))) -> begin
(

let uu____7328 = (

let uu____7335 = (translate_expr env e1)
in (

let uu____7336 = (translate_expr env e2)
in (

let uu____7337 = (translate_expr env e3)
in ((uu____7335), (uu____7336), (uu____7337)))))
in EBufWrite (uu____7328))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7339; FStar_Extraction_ML_Syntax.loc = uu____7340}, uu____7341); FStar_Extraction_ML_Syntax.mlty = uu____7342; FStar_Extraction_ML_Syntax.loc = uu____7343}, (e1)::(e2)::[]) when (

let uu____7352 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7352 "FStar.HyperStack.ST.op_Colon_Equals")) -> begin
(

let uu____7356 = (

let uu____7363 = (translate_expr env e1)
in (

let uu____7364 = (translate_expr env e2)
in ((uu____7363), (EConstant (((UInt32), ("0")))), (uu____7364))))
in EBufWrite (uu____7356))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7368; FStar_Extraction_ML_Syntax.loc = uu____7369}, (uu____7370)::[]) when (

let uu____7373 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7373 "FStar.HyperStack.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7378; FStar_Extraction_ML_Syntax.loc = uu____7379}, (uu____7380)::[]) when (

let uu____7383 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7383 "FStar.HyperStack.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7388; FStar_Extraction_ML_Syntax.loc = uu____7389}, uu____7390); FStar_Extraction_ML_Syntax.mlty = uu____7391; FStar_Extraction_ML_Syntax.loc = uu____7392}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (((

let uu____7406 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7406 "FStar.Buffer.blit")) || (

let uu____7411 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7411 "LowStar.Monotonic.Buffer.blit"))) || (

let uu____7416 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7416 "LowStar.UninitializedBuffer.ublit"))) -> begin
(

let uu____7420 = (

let uu____7431 = (translate_expr env e1)
in (

let uu____7432 = (translate_expr env e2)
in (

let uu____7433 = (translate_expr env e3)
in (

let uu____7434 = (translate_expr env e4)
in (

let uu____7435 = (translate_expr env e5)
in ((uu____7431), (uu____7432), (uu____7433), (uu____7434), (uu____7435)))))))
in EBufBlit (uu____7420))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7437; FStar_Extraction_ML_Syntax.loc = uu____7438}, uu____7439); FStar_Extraction_ML_Syntax.mlty = uu____7440; FStar_Extraction_ML_Syntax.loc = uu____7441}, (e1)::(e2)::(e3)::[]) when (

let s = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in ((Prims.op_Equality s "FStar.Buffer.fill") || (Prims.op_Equality s "LowStar.Monotonic.Buffer.fill"))) -> begin
(

let uu____7457 = (

let uu____7464 = (translate_expr env e1)
in (

let uu____7465 = (translate_expr env e2)
in (

let uu____7466 = (translate_expr env e3)
in ((uu____7464), (uu____7465), (uu____7466)))))
in EBufFill (uu____7457))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7468; FStar_Extraction_ML_Syntax.loc = uu____7469}, (uu____7470)::[]) when (

let uu____7473 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7473 "FStar.HyperStack.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7478; FStar_Extraction_ML_Syntax.loc = uu____7479}, uu____7480); FStar_Extraction_ML_Syntax.mlty = uu____7481; FStar_Extraction_ML_Syntax.loc = uu____7482}, (_ebuf)::(_eseq)::[]) when ((((

let uu____7493 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7493 "LowStar.Monotonic.Buffer.witness_p")) || (

let uu____7498 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7498 "LowStar.Monotonic.Buffer.recall_p"))) || (

let uu____7503 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7503 "LowStar.ImmutableBuffer.witness_contents"))) || (

let uu____7508 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7508 "LowStar.ImmutableBuffer.recall_contents"))) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7513; FStar_Extraction_ML_Syntax.loc = uu____7514}, (e1)::[]) when (

let uu____7518 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7518 "Obj.repr")) -> begin
(

let uu____7522 = (

let uu____7527 = (translate_expr env e1)
in ((uu____7527), (TAny)))
in ECast (uu____7522))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____7530; FStar_Extraction_ML_Syntax.loc = uu____7531}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____7547 = (FStar_Util.must (mk_width m))
in (

let uu____7548 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____7547 uu____7548 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____7550; FStar_Extraction_ML_Syntax.loc = uu____7551}, args) when (is_bool_op op) -> begin
(

let uu____7565 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____7565 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____7567; FStar_Extraction_ML_Syntax.loc = uu____7568}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____7570; FStar_Extraction_ML_Syntax.loc = uu____7571})::[]) when (is_machine_int m) -> begin
(

let uu____7596 = (

let uu____7602 = (FStar_Util.must (mk_width m))
in ((uu____7602), (c)))
in EConstant (uu____7596))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____7605; FStar_Extraction_ML_Syntax.loc = uu____7606}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____7608; FStar_Extraction_ML_Syntax.loc = uu____7609})::[]) when (is_machine_int m) -> begin
(

let uu____7634 = (

let uu____7640 = (FStar_Util.must (mk_width m))
in ((uu____7640), (c)))
in EConstant (uu____7634))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____7642; FStar_Extraction_ML_Syntax.loc = uu____7643}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____7645; FStar_Extraction_ML_Syntax.loc = uu____7646})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____7659 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::("Compat")::("String")::[], "of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____7661; FStar_Extraction_ML_Syntax.loc = uu____7662}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____7664; FStar_Extraction_ML_Syntax.loc = uu____7665})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____7682 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::("String")::[], "of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____7684; FStar_Extraction_ML_Syntax.loc = uu____7685}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____7687; FStar_Extraction_ML_Syntax.loc = uu____7688})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____7703 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____7706; FStar_Extraction_ML_Syntax.loc = uu____7707}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____7735 = (

let uu____7740 = (translate_expr env arg)
in ((uu____7740), (TInt (UInt64))))
in ECast (uu____7735))
end
| uu____7741 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____7745 = (

let uu____7750 = (translate_expr env arg)
in ((uu____7750), (TInt (UInt32))))
in ECast (uu____7745))
end
| uu____7751 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____7755 = (

let uu____7760 = (translate_expr env arg)
in ((uu____7760), (TInt (UInt16))))
in ECast (uu____7755))
end
| uu____7761 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____7765 = (

let uu____7770 = (translate_expr env arg)
in ((uu____7770), (TInt (UInt8))))
in ECast (uu____7765))
end
| uu____7771 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____7775 = (

let uu____7780 = (translate_expr env arg)
in ((uu____7780), (TInt (Int64))))
in ECast (uu____7775))
end
| uu____7781 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____7785 = (

let uu____7790 = (translate_expr env arg)
in ((uu____7790), (TInt (Int32))))
in ECast (uu____7785))
end
| uu____7791 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____7795 = (

let uu____7800 = (translate_expr env arg)
in ((uu____7800), (TInt (Int16))))
in ECast (uu____7795))
end
| uu____7801 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____7805 = (

let uu____7810 = (translate_expr env arg)
in ((uu____7810), (TInt (Int8))))
in ECast (uu____7805))
end
| uu____7811 -> begin
(

let uu____7813 = (

let uu____7820 = (

let uu____7823 = (translate_expr env arg)
in (uu____7823)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____7820)))
in EApp (uu____7813))
end)
end)
end)
end)
end)
end)
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, args) -> begin
(

let uu____7843 = (

let uu____7850 = (translate_expr env head1)
in (

let uu____7851 = (FStar_List.map (translate_expr env) args)
in ((uu____7850), (uu____7851))))
in EApp (uu____7843))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(

let uu____7862 = (

let uu____7869 = (translate_expr env head1)
in (

let uu____7870 = (FStar_List.map (translate_type env) ty_args)
in ((uu____7869), (uu____7870))))
in ETypApp (uu____7862))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) -> begin
(

let uu____7878 = (

let uu____7883 = (translate_expr env e1)
in (

let uu____7884 = (translate_type env t_to)
in ((uu____7883), (uu____7884))))
in ECast (uu____7878))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____7885, fields) -> begin
(

let uu____7907 = (

let uu____7919 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____7920 = (FStar_List.map (fun uu____7942 -> (match (uu____7942) with
| (field, expr) -> begin
(

let uu____7957 = (translate_expr env expr)
in ((field), (uu____7957)))
end)) fields)
in ((uu____7919), (uu____7920))))
in EFlat (uu____7907))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) -> begin
(

let uu____7968 = (

let uu____7976 = (assert_lid env e1.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____7977 = (translate_expr env e1)
in ((uu____7976), (uu____7977), ((FStar_Pervasives_Native.snd path)))))
in EField (uu____7968))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____7983) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, uu____7996) -> begin
(

let uu____8001 = (

let uu____8003 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head1)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____8003))
in (failwith uu____8001))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____8015 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____8015))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____8021 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____8021))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8024, cons1), es) -> begin
(

let uu____8039 = (

let uu____8049 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____8050 = (FStar_List.map (translate_expr env) es)
in ((uu____8049), (cons1), (uu____8050))))
in ECons (uu____8039))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env1 = (add_binders env args)
in (

let uu____8076 = (

let uu____8085 = (translate_expr env1 body)
in (

let uu____8086 = (translate_type env1 body.FStar_Extraction_ML_Syntax.mlty)
in ((binders), (uu____8085), (uu____8086))))
in EFun (uu____8076))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____8096 = (

let uu____8103 = (translate_expr env e1)
in (

let uu____8104 = (translate_expr env e2)
in (

let uu____8105 = (match (e3) with
| FStar_Pervasives_Native.None -> begin
EUnit
end
| FStar_Pervasives_Native.Some (e31) -> begin
(translate_expr env e31)
end)
in ((uu____8103), (uu____8104), (uu____8105)))))
in EIfThenElse (uu____8096))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____8107) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____8115) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____8131) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____8149 = (

let uu____8164 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____8164)))
in TApp (uu____8149))
end
| uu____8177 -> begin
TQualified (lid)
end)
end
| uu____8179 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____8206 -> (match (uu____8206) with
| (pat, guard, expr) -> begin
(match ((Prims.op_Equality guard FStar_Pervasives_Native.None)) with
| true -> begin
(

let uu____8233 = (translate_pat env pat)
in (match (uu____8233) with
| (env1, pat1) -> begin
(

let uu____8244 = (translate_expr env1 expr)
in ((pat1), (uu____8244)))
end))
end
| uu____8245 -> begin
(failwith "todo: translate_branch")
end)
end))
and translate_width : (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option  ->  width = (fun uu___290_8252 -> (match (uu___290_8252) with
| FStar_Pervasives_Native.None -> begin
CInt
end
| FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int8) -> begin
Int8
end
| FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int16) -> begin
Int16
end
| FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32) -> begin
Int32
end
| FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64) -> begin
Int64
end
| FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int8) -> begin
UInt8
end
| FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int16) -> begin
UInt16
end
| FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int32) -> begin
UInt32
end
| FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int64) -> begin
UInt64
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  (env * pattern) = (fun env p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
((env), (PUnit))
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (b)) -> begin
((env), (PBool (b)))
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Int (s, sw)) -> begin
(

let uu____8319 = (

let uu____8320 = (

let uu____8326 = (translate_width sw)
in ((uu____8326), (s)))
in PConstant (uu____8320))
in ((env), (uu____8319)))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name) -> begin
(

let env1 = (extend env name)
in ((env1), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env1 = (extend env "_")
in ((env1), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8336, cons1), ps) -> begin
(

let uu____8351 = (FStar_List.fold_left (fun uu____8371 p1 -> (match (uu____8371) with
| (env1, acc) -> begin
(

let uu____8391 = (translate_pat env1 p1)
in (match (uu____8391) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____8351) with
| (env1, ps1) -> begin
((env1), (PCons (((cons1), ((FStar_List.rev ps1))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____8421, ps) -> begin
(

let uu____8443 = (FStar_List.fold_left (fun uu____8480 uu____8481 -> (match (((uu____8480), (uu____8481))) with
| ((env1, acc), (field, p1)) -> begin
(

let uu____8561 = (translate_pat env1 p1)
in (match (uu____8561) with
| (env2, p2) -> begin
((env2), ((((field), (p2)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____8443) with
| (env1, ps1) -> begin
((env1), (PRecord ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____8632 = (FStar_List.fold_left (fun uu____8652 p1 -> (match (uu____8652) with
| (env1, acc) -> begin
(

let uu____8672 = (translate_pat env1 p1)
in (match (uu____8672) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____8632) with
| (env1, ps1) -> begin
((env1), (PTuple ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____8699) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____8705) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
((

let uu____8719 = (

let uu____8721 = (FStar_String.list_of_string s)
in (FStar_All.pipe_right uu____8721 (FStar_Util.for_some (fun c1 -> (Prims.op_Equality c1 (FStar_Char.char_of_int (Prims.parse_int "0")))))))
in (match (uu____8719) with
| true -> begin
(

let uu____8736 = (FStar_Util.format1 "Refusing to translate a string literal that contains a null character: %s" s)
in (failwith uu____8736))
end
| uu____8739 -> begin
()
end));
EString (s);
)
end
| FStar_Extraction_ML_Syntax.MLC_Char (c1) -> begin
(

let i = (FStar_Util.int_of_char c1)
in (

let s = (FStar_Util.string_of_int i)
in (

let c2 = EConstant (((UInt32), (s)))
in (

let char_of_int1 = EQualified (((("FStar")::("Char")::[]), ("char_of_int")))
in EApp (((char_of_int1), ((c2)::[])))))))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____8763)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____8781) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____8783) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) -> begin
EConstant (((CInt), (s)))
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____8807 = (

let uu____8814 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____8814)))
in EApp (uu____8807)))




