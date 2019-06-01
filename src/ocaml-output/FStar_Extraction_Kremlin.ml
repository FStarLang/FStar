
open Prims
open FStar_Pervasives
type decl =
| DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int * typ * expr)
| DFunction of (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ * (Prims.string Prims.list * Prims.string) * binder Prims.list * expr)
| DTypeAlias of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * typ)
| DTypeFlat of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list)
| DUnusedRetainedForBackwardsCompat of (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string Prims.list * Prims.string) * typ)
| DTypeVariant of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list)
| DTypeAbstractStruct of (Prims.string Prims.list * Prims.string)
| DExternal of (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string Prims.list * Prims.string) * typ * Prims.string Prims.list) 
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
| IfDef
| Macro 
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
| uu____732 -> begin
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
| uu____843 -> begin
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
| uu____968 -> begin
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
| uu____1075 -> begin
false
end))


let __proj__DTypeFlat__item___0 : decl  ->  ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list) = (fun projectee -> (match (projectee) with
| DTypeFlat (_0) -> begin
_0
end))


let uu___is_DUnusedRetainedForBackwardsCompat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DUnusedRetainedForBackwardsCompat (_0) -> begin
true
end
| uu____1207 -> begin
false
end))


let __proj__DUnusedRetainedForBackwardsCompat__item___0 : decl  ->  (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string Prims.list * Prims.string) * typ) = (fun projectee -> (match (projectee) with
| DUnusedRetainedForBackwardsCompat (_0) -> begin
_0
end))


let uu___is_DTypeVariant : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DTypeVariant (_0) -> begin
true
end
| uu____1324 -> begin
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
| uu____1465 -> begin
false
end))


let __proj__DTypeAbstractStruct__item___0 : decl  ->  (Prims.string Prims.list * Prims.string) = (fun projectee -> (match (projectee) with
| DTypeAbstractStruct (_0) -> begin
_0
end))


let uu___is_DExternal : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DExternal (_0) -> begin
true
end
| uu____1533 -> begin
false
end))


let __proj__DExternal__item___0 : decl  ->  (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string Prims.list * Prims.string) * typ * Prims.string Prims.list) = (fun projectee -> (match (projectee) with
| DExternal (_0) -> begin
_0
end))


let uu___is_StdCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| StdCall -> begin
true
end
| uu____1626 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____1637 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____1648 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1659 -> begin
false
end))


let uu___is_WipeBody : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WipeBody -> begin
true
end
| uu____1670 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1681 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1692 -> begin
false
end))


let uu___is_GCType : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GCType -> begin
true
end
| uu____1703 -> begin
false
end))


let uu___is_Comment : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____1716 -> begin
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
| uu____1737 -> begin
false
end))


let uu___is_Const : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____1750 -> begin
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
| uu____1773 -> begin
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
| uu____1796 -> begin
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
| uu____1817 -> begin
false
end))


let uu___is_IfDef : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| IfDef -> begin
true
end
| uu____1828 -> begin
false
end))


let uu___is_Macro : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Macro -> begin
true
end
| uu____1839 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____1850 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____1861 -> begin
false
end))


let uu___is_ManuallyManaged : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ManuallyManaged -> begin
true
end
| uu____1872 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____1885 -> begin
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
| uu____1915 -> begin
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
| uu____1963 -> begin
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
| uu____1996 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____2014 -> begin
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
| uu____2057 -> begin
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
| uu____2100 -> begin
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
| uu____2143 -> begin
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
| uu____2182 -> begin
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
| uu____2211 -> begin
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
| uu____2248 -> begin
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
| uu____2289 -> begin
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
| uu____2326 -> begin
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
| uu____2367 -> begin
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
| uu____2408 -> begin
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
| uu____2467 -> begin
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
| uu____2520 -> begin
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
| uu____2555 -> begin
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
| uu____2585 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____2596 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____2609 -> begin
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
| uu____2630 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____2641 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____2653 -> begin
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
| uu____2683 -> begin
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
| uu____2742 -> begin
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
| uu____2786 -> begin
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
| uu____2823 -> begin
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
| uu____2862 -> begin
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
| uu____2896 -> begin
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
| uu____2948 -> begin
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
| uu____2986 -> begin
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
| uu____3016 -> begin
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
| uu____3060 -> begin
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
| uu____3082 -> begin
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
| uu____3105 -> begin
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
| uu____3135 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____3146 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____3157 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____3168 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____3179 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____3190 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____3201 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____3212 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____3223 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____3234 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____3245 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____3256 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____3267 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____3278 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____3289 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____3300 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____3311 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____3322 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____3333 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____3344 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____3355 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____3366 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____3377 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____3388 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____3399 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____3410 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____3423 -> begin
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
| uu____3445 -> begin
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
| uu____3471 -> begin
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
| uu____3513 -> begin
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
| uu____3545 -> begin
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
| uu____3590 -> begin
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
| uu____3623 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____3634 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____3645 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____3656 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____3667 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____3678 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____3689 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____3700 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____3711 -> begin
false
end))


let uu___is_CInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInt -> begin
true
end
| uu____3722 -> begin
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
| uu____3771 -> begin
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
| uu____3790 -> begin
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
| uu____3808 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____3828 -> begin
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
| uu____3870 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____3881 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____3897 -> begin
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
| uu____3929 -> begin
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
| uu____3965 -> begin
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
| uu____4028 -> begin
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


let fst3 : 'Auu____4129 'Auu____4130 'Auu____4131 . ('Auu____4129 * 'Auu____4130 * 'Auu____4131)  ->  'Auu____4129 = (fun uu____4142 -> (match (uu____4142) with
| (x, uu____4150, uu____4151) -> begin
x
end))


let snd3 : 'Auu____4161 'Auu____4162 'Auu____4163 . ('Auu____4161 * 'Auu____4162 * 'Auu____4163)  ->  'Auu____4162 = (fun uu____4174 -> (match (uu____4174) with
| (uu____4181, x, uu____4183) -> begin
x
end))


let thd3 : 'Auu____4193 'Auu____4194 'Auu____4195 . ('Auu____4193 * 'Auu____4194 * 'Auu____4195)  ->  'Auu____4195 = (fun uu____4206 -> (match (uu____4206) with
| (uu____4213, uu____4214, x) -> begin
x
end))


let mk_width : Prims.string  ->  width FStar_Pervasives_Native.option = (fun uu___0_4224 -> (match (uu___0_4224) with
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
| uu____4236 -> begin
FStar_Pervasives_Native.None
end))


let mk_bool_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___1_4246 -> (match (uu___1_4246) with
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
| uu____4255 -> begin
FStar_Pervasives_Native.None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> (Prims.op_disEquality (mk_bool_op op) FStar_Pervasives_Native.None))


let mk_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___2_4276 -> (match (uu___2_4276) with
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
| uu____4321 -> begin
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

let uu___163_4477 = env
in {names = ({pretty = x})::env.names; names_t = uu___163_4477.names_t; module_name = uu___163_4477.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___167_4491 = env
in {names = uu___167_4491.names; names_t = (x)::env.names_t; module_name = uu___167_4491.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____4506 = (FStar_List.tryFind (fun name -> (Prims.op_Equality name.pretty x)) env.names)
in (match (uu____4506) with
| FStar_Pervasives_Native.Some (name) -> begin
name
end
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: name not found")
end)))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_All.try_with (fun uu___178_4530 -> (match (()) with
| () -> begin
(FStar_List.index (fun name -> (Prims.op_Equality name.pretty x)) env.names)
end)) (fun uu___177_4537 -> (

let uu____4539 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____4539)))))


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_All.try_with (fun uu___187_4559 -> (match (()) with
| () -> begin
(FStar_List.index (fun name -> (Prims.op_Equality name x)) env.names_t)
end)) (fun uu___186_4568 -> (

let uu____4570 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____4570)))))


let add_binders : 'Auu____4581 . env  ->  (Prims.string * 'Auu____4581) Prims.list  ->  env = (fun env binders -> (FStar_List.fold_left (fun env1 uu____4616 -> (match (uu____4616) with
| (name, uu____4623) -> begin
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
| uu____4675 -> begin
(failwith "Argument of FStar.Buffer.createL is not a list literal!")
end))
in (list_elements [] e2)))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____4894 -> (match (uu____4894) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____4943 = m
in (match (uu____4943) with
| (path, uu____4958, uu____4959) -> begin
(FStar_Extraction_ML_Syntax.string_of_mlpath path)
end))
in (FStar_All.try_with (fun uu___229_4977 -> (match (()) with
| () -> begin
((

let uu____4981 = (

let uu____4983 = (FStar_Options.silent ())
in (not (uu____4983)))
in (match (uu____4981) with
| true -> begin
(FStar_Util.print1 "Attempting to translate module %s\n" m_name)
end
| uu____4987 -> begin
()
end));
(

let uu____4989 = (translate_module m)
in FStar_Pervasives_Native.Some (uu____4989));
)
end)) (fun uu___228_4993 -> (match (uu___228_4993) with
| e -> begin
((

let uu____4998 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____4998));
FStar_Pervasives_Native.None;
)
end))))) modules)
end))
and translate_module : (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____5001 -> (match (uu____5001) with
| (module_name, modul, uu____5016) -> begin
(

let module_name1 = (FStar_List.append (FStar_Pervasives_Native.fst module_name) (((FStar_Pervasives_Native.snd module_name))::[]))
in (

let program = (match (modul) with
| FStar_Pervasives_Native.Some (_signature, decls) -> begin
(FStar_List.collect (translate_decl (empty module_name1)) decls)
end
| uu____5051 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name1)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.meta Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun uu___3_5065 -> (match (uu___3_5065) with
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
| FStar_Extraction_ML_Syntax.CIfDef -> begin
FStar_Pervasives_Native.Some (IfDef)
end
| FStar_Extraction_ML_Syntax.CMacro -> begin
FStar_Pervasives_Native.Some (Macro)
end
| uu____5076 -> begin
FStar_Pervasives_Native.None
end)) flags))
and translate_cc : FStar_Extraction_ML_Syntax.meta Prims.list  ->  cc FStar_Pervasives_Native.option = (fun flags -> (

let uu____5080 = (FStar_List.choose (fun uu___4_5087 -> (match (uu___4_5087) with
| FStar_Extraction_ML_Syntax.CCConv (s) -> begin
FStar_Pervasives_Native.Some (s)
end
| uu____5094 -> begin
FStar_Pervasives_Native.None
end)) flags)
in (match (uu____5080) with
| ("stdcall")::[] -> begin
FStar_Pervasives_Native.Some (StdCall)
end
| ("fastcall")::[] -> begin
FStar_Pervasives_Native.Some (FastCall)
end
| ("cdecl")::[] -> begin
FStar_Pervasives_Native.Some (CDecl)
end
| uu____5107 -> begin
FStar_Pervasives_Native.None
end)))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.list = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) -> begin
(FStar_List.choose (translate_let env flavor) lbs)
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____5121) -> begin
[]
end
| FStar_Extraction_ML_Syntax.MLM_Ty (tys) -> begin
(FStar_List.choose (translate_type_decl env) tys)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____5123) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____5128) -> begin
((FStar_Util.print1_warning "Not extracting exception %s to KreMLin (exceptions unsupported)\n" m);
[];
)
end))
and translate_let : env  ->  FStar_Extraction_ML_Syntax.mlletflavor  ->  FStar_Extraction_ML_Syntax.mllb  ->  decl FStar_Pervasives_Native.option = (fun env flavor lb -> (match (lb) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5155; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____5158} when (FStar_Util.for_some (fun uu___5_5163 -> (match (uu___5_5163) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____5166 -> begin
false
end)) meta) -> begin
(

let name1 = ((env.module_name), (name))
in (

let arg_names = (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (args, uu____5189) -> begin
(FStar_List.map FStar_Pervasives_Native.fst args)
end
| uu____5211 -> begin
[]
end)
in (match ((Prims.op_Equality (FStar_List.length tvars) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5219 = (

let uu____5220 = (

let uu____5246 = (translate_cc meta)
in (

let uu____5249 = (translate_flags meta)
in (

let uu____5252 = (translate_type env t0)
in ((uu____5246), (uu____5249), (name1), (uu____5252), (arg_names)))))
in DExternal (uu____5220))
in FStar_Pervasives_Native.Some (uu____5219))
end
| uu____5268 -> begin
((

let uu____5271 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print1_warning "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n" uu____5271));
FStar_Pervasives_Native.None;
)
end)))
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5277; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____5280; FStar_Extraction_ML_Syntax.loc = uu____5281}; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____5283} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5304 -> begin
(

let env1 = (match ((Prims.op_Equality flavor FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name)
end
| uu____5308 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 name1 -> (extend_t env2 name1)) env1 tvars)
in (

let rec find_return_type = (fun eff i uu___6_5340 -> (match (uu___6_5340) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5349, eff1, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type eff1 (i - (Prims.parse_int "1")) t)
end
| t -> begin
((i), (eff), (t))
end))
in (

let name1 = ((env2.module_name), (name))
in (

let uu____5369 = (find_return_type FStar_Extraction_ML_Syntax.E_PURE (FStar_List.length args) t0)
in (match (uu____5369) with
| (i, eff, t) -> begin
((match ((i > (Prims.parse_int "0"))) with
| true -> begin
(

let msg = "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
in (

let uu____5395 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print2_warning "Not extracting %s to KreMLin (%s)\n" uu____5395 msg)))
end
| uu____5398 -> begin
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
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____5413) -> begin
(

let uu____5414 = (translate_flags meta)
in (MustDisappear)::uu____5414)
end
| (FStar_Extraction_ML_Syntax.E_PURE, TUnit) -> begin
(

let uu____5417 = (translate_flags meta)
in (MustDisappear)::uu____5417)
end
| uu____5420 -> begin
(translate_flags meta)
end)
in (FStar_All.try_with (fun uu___375_5429 -> (match (()) with
| () -> begin
(

let body1 = (translate_expr env3 body)
in FStar_Pervasives_Native.Some (DFunction (((cc), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (body1)))))
end)) (fun uu___374_5454 -> (match (uu___374_5454) with
| e -> begin
(

let msg = (FStar_Util.print_exn e)
in ((

let uu____5461 = (

let uu____5467 = (

let uu____5469 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.format2 "Error while extracting %s to KreMLin (%s)\n" uu____5469 msg))
in ((FStar_Errors.Warning_FunctionNotExtacted), (uu____5467)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____5461));
(

let msg1 = (Prims.op_Hat "This function was not extracted:\n" msg)
in FStar_Pervasives_Native.Some (DFunction (((cc), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (EAbortS (msg1))))));
))
end))))))));
)
end))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5495; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____5498} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5505 -> begin
(

let meta1 = (translate_flags meta)
in (

let env1 = (FStar_List.fold_left (fun env1 name1 -> (extend_t env1 name1)) env tvars)
in (

let t1 = (translate_type env1 t)
in (

let name1 = ((env1.module_name), (name))
in (FStar_All.try_with (fun uu___402_5535 -> (match (()) with
| () -> begin
(

let expr1 = (translate_expr env1 expr)
in FStar_Pervasives_Native.Some (DGlobal (((meta1), (name1), ((FStar_List.length tvars)), (t1), (expr1)))))
end)) (fun uu___401_5554 -> (match (uu___401_5554) with
| e -> begin
((

let uu____5559 = (

let uu____5565 = (

let uu____5567 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (

let uu____5569 = (FStar_Util.print_exn e)
in (FStar_Util.format2 "Error extracting %s to KreMLin (%s)\n" uu____5567 uu____5569)))
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____5565)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____5559));
FStar_Pervasives_Native.Some (DGlobal (((meta1), (name1), ((FStar_List.length tvars)), (t1), (EAny))));
)
end)))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5587; FStar_Extraction_ML_Syntax.mllb_def = uu____5588; FStar_Extraction_ML_Syntax.mllb_meta = uu____5589; FStar_Extraction_ML_Syntax.print_typ = uu____5590} -> begin
((

let uu____5597 = (

let uu____5603 = (FStar_Util.format1 "Not extracting %s to KreMLin\n" name)
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____5603)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____5597));
(match (ts) with
| FStar_Pervasives_Native.Some (idents, t) -> begin
(

let uu____5610 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" (FStar_String.concat ", " idents) uu____5610))
end
| FStar_Pervasives_Native.None -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
and translate_type_decl : env  ->  FStar_Extraction_ML_Syntax.one_mltydecl  ->  decl FStar_Pervasives_Native.option = (fun env ty -> (

let uu____5624 = ty
in (match (uu____5624) with
| (uu____5627, uu____5628, uu____5629, uu____5630, flags, uu____5632) -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5650 -> begin
(match (ty) with
| (assumed, name, _mangled_name, args, flags1, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 name2 -> (extend_t env1 name2)) env args)
in (match ((assumed && (FStar_List.mem FStar_Extraction_ML_Syntax.CAbstract flags1))) with
| true -> begin
FStar_Pervasives_Native.Some (DTypeAbstractStruct (name1))
end
| uu____5695 -> begin
(match (assumed) with
| true -> begin
(

let name2 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in ((FStar_Util.print1_warning "Not extracting type definition %s to KreMLin (assumed type)\n" name2);
FStar_Pervasives_Native.None;
))
end
| uu____5704 -> begin
(

let uu____5706 = (

let uu____5707 = (

let uu____5727 = (translate_flags flags1)
in (

let uu____5730 = (translate_type env1 t)
in ((name1), (uu____5727), ((FStar_List.length args)), (uu____5730))))
in DTypeAlias (uu____5707))
in FStar_Pervasives_Native.Some (uu____5706))
end)
end)))
end
| (uu____5743, name, _mangled_name, args, flags1, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 name2 -> (extend_t env1 name2)) env args)
in (

let uu____5788 = (

let uu____5789 = (

let uu____5821 = (translate_flags flags1)
in (

let uu____5824 = (FStar_List.map (fun uu____5856 -> (match (uu____5856) with
| (f, t) -> begin
(

let uu____5876 = (

let uu____5882 = (translate_type env1 t)
in ((uu____5882), (false)))
in ((f), (uu____5876)))
end)) fields)
in ((name1), (uu____5821), ((FStar_List.length args)), (uu____5824))))
in DTypeFlat (uu____5789))
in FStar_Pervasives_Native.Some (uu____5788))))
end
| (uu____5915, name, _mangled_name, args, flags1, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let flags2 = (translate_flags flags1)
in (

let env1 = (FStar_List.fold_left extend_t env args)
in (

let uu____5965 = (

let uu____5966 = (

let uu____6005 = (FStar_List.map (fun uu____6058 -> (match (uu____6058) with
| (cons1, ts) -> begin
(

let uu____6106 = (FStar_List.map (fun uu____6138 -> (match (uu____6138) with
| (name2, t) -> begin
(

let uu____6158 = (

let uu____6164 = (translate_type env1 t)
in ((uu____6164), (false)))
in ((name2), (uu____6158)))
end)) ts)
in ((cons1), (uu____6106)))
end)) branches)
in ((name1), (flags2), ((FStar_List.length args)), (uu____6005)))
in DTypeVariant (uu____5966))
in FStar_Pervasives_Native.Some (uu____5965)))))
end
| (uu____6217, name, _mangled_name, uu____6220, uu____6221, uu____6222) -> begin
((

let uu____6238 = (

let uu____6244 = (FStar_Util.format1 "Error extracting type definition %s to KreMLin\n" name)
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____6244)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____6238));
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

let uu____6252 = (find_t env name)
in TBound (uu____6252))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____6255, t2) -> begin
(

let uu____6257 = (

let uu____6262 = (translate_type env t1)
in (

let uu____6263 = (translate_type env t2)
in ((uu____6262), (uu____6263))))
in TArrow (uu____6257))
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____6267 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6267 "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____6274 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6274 "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____6291 = (FStar_Util.must (mk_width m))
in TInt (uu____6291))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____6305 = (FStar_Util.must (mk_width m))
in TInt (uu____6305))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____6310 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6310 "FStar.Monotonic.HyperStack.mem")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____6314)::(arg)::(uu____6316)::[], p) when ((((

let uu____6322 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6322 "FStar.Monotonic.HyperStack.s_mref")) || (

let uu____6327 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6327 "FStar.Monotonic.HyperHeap.mrref"))) || (

let uu____6332 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6332 "FStar.HyperStack.ST.m_rref"))) || (

let uu____6337 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6337 "FStar.HyperStack.ST.s_mref"))) -> begin
(

let uu____6341 = (translate_type env arg)
in TBuf (uu____6341))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::(uu____6343)::[], p) when (((((((((((

let uu____6349 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6349 "FStar.Monotonic.HyperStack.mreference")) || (

let uu____6354 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6354 "FStar.Monotonic.HyperStack.mstackref"))) || (

let uu____6359 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6359 "FStar.Monotonic.HyperStack.mref"))) || (

let uu____6364 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6364 "FStar.Monotonic.HyperStack.mmmstackref"))) || (

let uu____6369 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6369 "FStar.Monotonic.HyperStack.mmmref"))) || (

let uu____6374 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6374 "FStar.Monotonic.Heap.mref"))) || (

let uu____6379 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6379 "FStar.HyperStack.ST.mreference"))) || (

let uu____6384 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6384 "FStar.HyperStack.ST.mstackref"))) || (

let uu____6389 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6389 "FStar.HyperStack.ST.mref"))) || (

let uu____6394 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6394 "FStar.HyperStack.ST.mmmstackref"))) || (

let uu____6399 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6399 "FStar.HyperStack.ST.mmmref"))) -> begin
(

let uu____6403 = (translate_type env arg)
in TBuf (uu____6403))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::(uu____6405)::(uu____6406)::[], p) when (

let uu____6410 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6410 "LowStar.Monotonic.Buffer.mbuffer")) -> begin
(

let uu____6414 = (translate_type env arg)
in TBuf (uu____6414))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((((((((((((((

let uu____6421 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6421 "FStar.Buffer.buffer")) || (

let uu____6426 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6426 "LowStar.Buffer.buffer"))) || (

let uu____6431 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6431 "LowStar.ImmutableBuffer.ibuffer"))) || (

let uu____6436 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6436 "LowStar.UninitializedBuffer.ubuffer"))) || (

let uu____6441 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6441 "FStar.HyperStack.reference"))) || (

let uu____6446 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6446 "FStar.HyperStack.stackref"))) || (

let uu____6451 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6451 "FStar.HyperStack.ref"))) || (

let uu____6456 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6456 "FStar.HyperStack.mmstackref"))) || (

let uu____6461 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6461 "FStar.HyperStack.mmref"))) || (

let uu____6466 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6466 "FStar.HyperStack.ST.reference"))) || (

let uu____6471 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6471 "FStar.HyperStack.ST.stackref"))) || (

let uu____6476 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6476 "FStar.HyperStack.ST.ref"))) || (

let uu____6481 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6481 "FStar.HyperStack.ST.mmstackref"))) || (

let uu____6486 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6486 "FStar.HyperStack.ST.mmref"))) -> begin
(

let uu____6490 = (translate_type env arg)
in TBuf (uu____6490))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____6491)::(arg)::[], p) when ((

let uu____6498 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6498 "FStar.HyperStack.s_ref")) || (

let uu____6503 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6503 "FStar.HyperStack.ST.s_ref"))) -> begin
(

let uu____6507 = (translate_type env arg)
in TBuf (uu____6507))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____6508)::[], p) when (

let uu____6512 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6512 "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when (((Prims.op_Equality ns (("Prims")::[])) || (Prims.op_Equality ns (("FStar")::("Pervasives")::("Native")::[]))) && (FStar_Util.starts_with t1 "tuple")) -> begin
(

let uu____6564 = (FStar_List.map (translate_type env) args)
in TTuple (uu____6564))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6575 = (

let uu____6590 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____6590)))
in TApp (uu____6575))
end
| uu____6603 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____6608 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____6608))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____6626 -> (match (uu____6626) with
| (name, typ) -> begin
(

let uu____6636 = (translate_type env typ)
in {name = name; typ = uu____6636; mut = false})
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

let uu____6643 = (find env name)
in EBound (uu____6643))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____6657 = (

let uu____6662 = (FStar_Util.must (mk_op op))
in (

let uu____6663 = (FStar_Util.must (mk_width m))
in ((uu____6662), (uu____6663))))
in EOp (uu____6657))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____6673 = (

let uu____6678 = (FStar_Util.must (mk_bool_op op))
in ((uu____6678), (Bool)))
in EOp (uu____6673))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n1) -> begin
EQualified (n1)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.mllb_meta = flags; FStar_Extraction_ML_Syntax.print_typ = print7})::[]), continuation) -> begin
(

let binder = (

let uu____6701 = (translate_type env typ)
in {name = name; typ = uu____6701; mut = false})
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

let uu____6728 = (

let uu____6739 = (translate_expr env expr)
in (

let uu____6740 = (translate_branches env branches)
in ((uu____6739), (uu____6740))))
in EMatch (uu____6728))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6754; FStar_Extraction_ML_Syntax.loc = uu____6755}, (t)::[]); FStar_Extraction_ML_Syntax.mlty = uu____6757; FStar_Extraction_ML_Syntax.loc = uu____6758}, (arg)::[]) when (

let uu____6764 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6764 "FStar.Dyn.undyn")) -> begin
(

let uu____6768 = (

let uu____6773 = (translate_expr env arg)
in (

let uu____6774 = (translate_type env t)
in ((uu____6773), (uu____6774))))
in ECast (uu____6768))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6776; FStar_Extraction_ML_Syntax.loc = uu____6777}, uu____6778); FStar_Extraction_ML_Syntax.mlty = uu____6779; FStar_Extraction_ML_Syntax.loc = uu____6780}, uu____6781) when (

let uu____6790 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6790 "Prims.admit")) -> begin
EAbort
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6795; FStar_Extraction_ML_Syntax.loc = uu____6796}, uu____6797); FStar_Extraction_ML_Syntax.mlty = uu____6798; FStar_Extraction_ML_Syntax.loc = uu____6799}, (arg)::[]) when (((

let uu____6809 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6809 "FStar.HyperStack.All.failwith")) || (

let uu____6814 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6814 "FStar.Error.unexpected"))) || (

let uu____6819 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6819 "FStar.Error.unreachable"))) -> begin
(match (arg) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (msg)); FStar_Extraction_ML_Syntax.mlty = uu____6824; FStar_Extraction_ML_Syntax.loc = uu____6825} -> begin
EAbortS (msg)
end
| uu____6827 -> begin
(

let print7 = (

let uu____6829 = (

let uu____6830 = (

let uu____6831 = (FStar_Ident.lid_of_str "FStar.HyperStack.IO.print_string")
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6831))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____6830))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____6829))
in (

let print8 = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top (FStar_Extraction_ML_Syntax.MLE_App (((print7), ((arg)::[])))))
in (

let t = (translate_expr env print8)
in ESequence ((t)::(EAbort)::[]))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6838; FStar_Extraction_ML_Syntax.loc = uu____6839}, uu____6840); FStar_Extraction_ML_Syntax.mlty = uu____6841; FStar_Extraction_ML_Syntax.loc = uu____6842}, (e1)::[]) when ((

let uu____6852 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6852 "LowStar.ToFStarBuffer.new_to_old_st")) || (

let uu____6857 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6857 "LowStar.ToFStarBuffer.old_to_new_st"))) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6862; FStar_Extraction_ML_Syntax.loc = uu____6863}, uu____6864); FStar_Extraction_ML_Syntax.mlty = uu____6865; FStar_Extraction_ML_Syntax.loc = uu____6866}, (e1)::(e2)::[]) when ((((

let uu____6877 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6877 "FStar.Buffer.index")) || (

let uu____6882 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6882 "FStar.Buffer.op_Array_Access"))) || (

let uu____6887 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6887 "LowStar.Monotonic.Buffer.index"))) || (

let uu____6892 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6892 "LowStar.UninitializedBuffer.uindex"))) -> begin
(

let uu____6896 = (

let uu____6901 = (translate_expr env e1)
in (

let uu____6902 = (translate_expr env e2)
in ((uu____6901), (uu____6902))))
in EBufRead (uu____6896))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6904; FStar_Extraction_ML_Syntax.loc = uu____6905}, uu____6906); FStar_Extraction_ML_Syntax.mlty = uu____6907; FStar_Extraction_ML_Syntax.loc = uu____6908}, (e1)::[]) when (

let uu____6916 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6916 "FStar.HyperStack.ST.op_Bang")) -> begin
(

let uu____6920 = (

let uu____6925 = (translate_expr env e1)
in ((uu____6925), (EConstant (((UInt32), ("0"))))))
in EBufRead (uu____6920))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6929; FStar_Extraction_ML_Syntax.loc = uu____6930}, uu____6931); FStar_Extraction_ML_Syntax.mlty = uu____6932; FStar_Extraction_ML_Syntax.loc = uu____6933}, (e1)::(e2)::[]) when (((

let uu____6944 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6944 "FStar.Buffer.create")) || (

let uu____6949 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6949 "LowStar.Monotonic.Buffer.malloca"))) || (

let uu____6954 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6954 "LowStar.ImmutableBuffer.ialloca"))) -> begin
(

let uu____6958 = (

let uu____6965 = (translate_expr env e1)
in (

let uu____6966 = (translate_expr env e2)
in ((Stack), (uu____6965), (uu____6966))))
in EBufCreate (uu____6958))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6968; FStar_Extraction_ML_Syntax.loc = uu____6969}, uu____6970); FStar_Extraction_ML_Syntax.mlty = uu____6971; FStar_Extraction_ML_Syntax.loc = uu____6972}, (elen)::[]) when (

let uu____6980 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____6980 "LowStar.UninitializedBuffer.ualloca")) -> begin
(

let uu____6984 = (

let uu____6989 = (translate_expr env elen)
in ((Stack), (uu____6989)))
in EBufCreateNoInit (uu____6984))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____6991; FStar_Extraction_ML_Syntax.loc = uu____6992}, uu____6993); FStar_Extraction_ML_Syntax.mlty = uu____6994; FStar_Extraction_ML_Syntax.loc = uu____6995}, (init1)::[]) when (

let uu____7003 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7003 "FStar.HyperStack.ST.salloc")) -> begin
(

let uu____7007 = (

let uu____7014 = (translate_expr env init1)
in ((Stack), (uu____7014), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____7007))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7018; FStar_Extraction_ML_Syntax.loc = uu____7019}, uu____7020); FStar_Extraction_ML_Syntax.mlty = uu____7021; FStar_Extraction_ML_Syntax.loc = uu____7022}, (e2)::[]) when (((

let uu____7032 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7032 "FStar.Buffer.createL")) || (

let uu____7037 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7037 "LowStar.Monotonic.Buffer.malloca_of_list"))) || (

let uu____7042 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7042 "LowStar.ImmutableBuffer.ialloca_of_list"))) -> begin
(

let uu____7046 = (

let uu____7053 = (

let uu____7056 = (list_elements e2)
in (FStar_List.map (translate_expr env) uu____7056))
in ((Stack), (uu____7053)))
in EBufCreateL (uu____7046))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7062; FStar_Extraction_ML_Syntax.loc = uu____7063}, uu____7064); FStar_Extraction_ML_Syntax.mlty = uu____7065; FStar_Extraction_ML_Syntax.loc = uu____7066}, (_erid)::(e2)::[]) when ((

let uu____7077 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7077 "LowStar.Monotonic.Buffer.mgcmalloc_of_list")) || (

let uu____7082 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7082 "LowStar.ImmutableBuffer.igcmalloc_of_list"))) -> begin
(

let uu____7086 = (

let uu____7093 = (

let uu____7096 = (list_elements e2)
in (FStar_List.map (translate_expr env) uu____7096))
in ((Eternal), (uu____7093)))
in EBufCreateL (uu____7086))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7102; FStar_Extraction_ML_Syntax.loc = uu____7103}, uu____7104); FStar_Extraction_ML_Syntax.mlty = uu____7105; FStar_Extraction_ML_Syntax.loc = uu____7106}, (_rid)::(init1)::[]) when (

let uu____7115 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7115 "FStar.HyperStack.ST.ralloc")) -> begin
(

let uu____7119 = (

let uu____7126 = (translate_expr env init1)
in ((Eternal), (uu____7126), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____7119))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7130; FStar_Extraction_ML_Syntax.loc = uu____7131}, uu____7132); FStar_Extraction_ML_Syntax.mlty = uu____7133; FStar_Extraction_ML_Syntax.loc = uu____7134}, (_e0)::(e1)::(e2)::[]) when (((

let uu____7146 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7146 "FStar.Buffer.rcreate")) || (

let uu____7151 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7151 "LowStar.Monotonic.Buffer.mgcmalloc"))) || (

let uu____7156 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7156 "LowStar.ImmutableBuffer.igcmalloc"))) -> begin
(

let uu____7160 = (

let uu____7167 = (translate_expr env e1)
in (

let uu____7168 = (translate_expr env e2)
in ((Eternal), (uu____7167), (uu____7168))))
in EBufCreate (uu____7160))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7170; FStar_Extraction_ML_Syntax.loc = uu____7171}, uu____7172); FStar_Extraction_ML_Syntax.mlty = uu____7173; FStar_Extraction_ML_Syntax.loc = uu____7174}, (_erid)::(elen)::[]) when (

let uu____7183 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7183 "LowStar.UninitializedBuffer.ugcmalloc")) -> begin
(

let uu____7187 = (

let uu____7192 = (translate_expr env elen)
in ((Eternal), (uu____7192)))
in EBufCreateNoInit (uu____7187))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7194; FStar_Extraction_ML_Syntax.loc = uu____7195}, uu____7196); FStar_Extraction_ML_Syntax.mlty = uu____7197; FStar_Extraction_ML_Syntax.loc = uu____7198}, (_rid)::(init1)::[]) when (

let uu____7207 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7207 "FStar.HyperStack.ST.ralloc_mm")) -> begin
(

let uu____7211 = (

let uu____7218 = (translate_expr env init1)
in ((ManuallyManaged), (uu____7218), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____7211))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7222; FStar_Extraction_ML_Syntax.loc = uu____7223}, uu____7224); FStar_Extraction_ML_Syntax.mlty = uu____7225; FStar_Extraction_ML_Syntax.loc = uu____7226}, (_e0)::(e1)::(e2)::[]) when ((((

let uu____7238 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7238 "FStar.Buffer.rcreate_mm")) || (

let uu____7243 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7243 "LowStar.Monotonic.Buffer.mmalloc"))) || (

let uu____7248 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7248 "LowStar.Monotonic.Buffer.mmalloc"))) || (

let uu____7253 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7253 "LowStar.ImmutableBuffer.imalloc"))) -> begin
(

let uu____7257 = (

let uu____7264 = (translate_expr env e1)
in (

let uu____7265 = (translate_expr env e2)
in ((ManuallyManaged), (uu____7264), (uu____7265))))
in EBufCreate (uu____7257))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7267; FStar_Extraction_ML_Syntax.loc = uu____7268}, uu____7269); FStar_Extraction_ML_Syntax.mlty = uu____7270; FStar_Extraction_ML_Syntax.loc = uu____7271}, (_erid)::(elen)::[]) when (

let uu____7280 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7280 "LowStar.UninitializedBuffer.umalloc")) -> begin
(

let uu____7284 = (

let uu____7289 = (translate_expr env elen)
in ((ManuallyManaged), (uu____7289)))
in EBufCreateNoInit (uu____7284))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7291; FStar_Extraction_ML_Syntax.loc = uu____7292}, uu____7293); FStar_Extraction_ML_Syntax.mlty = uu____7294; FStar_Extraction_ML_Syntax.loc = uu____7295}, (e2)::[]) when (

let uu____7303 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7303 "FStar.HyperStack.ST.rfree")) -> begin
(

let uu____7307 = (translate_expr env e2)
in EBufFree (uu____7307))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7309; FStar_Extraction_ML_Syntax.loc = uu____7310}, uu____7311); FStar_Extraction_ML_Syntax.mlty = uu____7312; FStar_Extraction_ML_Syntax.loc = uu____7313}, (e2)::[]) when ((

let uu____7323 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7323 "FStar.Buffer.rfree")) || (

let uu____7328 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7328 "LowStar.Monotonic.Buffer.free"))) -> begin
(

let uu____7332 = (translate_expr env e2)
in EBufFree (uu____7332))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7334; FStar_Extraction_ML_Syntax.loc = uu____7335}, uu____7336); FStar_Extraction_ML_Syntax.mlty = uu____7337; FStar_Extraction_ML_Syntax.loc = uu____7338}, (e1)::(e2)::(_e3)::[]) when (

let uu____7348 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7348 "FStar.Buffer.sub")) -> begin
(

let uu____7352 = (

let uu____7357 = (translate_expr env e1)
in (

let uu____7358 = (translate_expr env e2)
in ((uu____7357), (uu____7358))))
in EBufSub (uu____7352))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7360; FStar_Extraction_ML_Syntax.loc = uu____7361}, uu____7362); FStar_Extraction_ML_Syntax.mlty = uu____7363; FStar_Extraction_ML_Syntax.loc = uu____7364}, (e1)::(e2)::(_e3)::[]) when (

let uu____7374 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7374 "LowStar.Monotonic.Buffer.msub")) -> begin
(

let uu____7378 = (

let uu____7383 = (translate_expr env e1)
in (

let uu____7384 = (translate_expr env e2)
in ((uu____7383), (uu____7384))))
in EBufSub (uu____7378))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7386; FStar_Extraction_ML_Syntax.loc = uu____7387}, uu____7388); FStar_Extraction_ML_Syntax.mlty = uu____7389; FStar_Extraction_ML_Syntax.loc = uu____7390}, (e1)::(e2)::[]) when (

let uu____7399 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7399 "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7404; FStar_Extraction_ML_Syntax.loc = uu____7405}, uu____7406); FStar_Extraction_ML_Syntax.mlty = uu____7407; FStar_Extraction_ML_Syntax.loc = uu____7408}, (e1)::(e2)::[]) when (

let uu____7417 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7417 "FStar.Buffer.offset")) -> begin
(

let uu____7421 = (

let uu____7426 = (translate_expr env e1)
in (

let uu____7427 = (translate_expr env e2)
in ((uu____7426), (uu____7427))))
in EBufSub (uu____7421))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7429; FStar_Extraction_ML_Syntax.loc = uu____7430}, uu____7431); FStar_Extraction_ML_Syntax.mlty = uu____7432; FStar_Extraction_ML_Syntax.loc = uu____7433}, (e1)::(e2)::[]) when (

let uu____7442 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7442 "LowStar.Monotonic.Buffer.moffset")) -> begin
(

let uu____7446 = (

let uu____7451 = (translate_expr env e1)
in (

let uu____7452 = (translate_expr env e2)
in ((uu____7451), (uu____7452))))
in EBufSub (uu____7446))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7454; FStar_Extraction_ML_Syntax.loc = uu____7455}, uu____7456); FStar_Extraction_ML_Syntax.mlty = uu____7457; FStar_Extraction_ML_Syntax.loc = uu____7458}, (e1)::(e2)::(e3)::[]) when ((((

let uu____7470 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7470 "FStar.Buffer.upd")) || (

let uu____7475 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7475 "FStar.Buffer.op_Array_Assignment"))) || (

let uu____7480 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7480 "LowStar.Monotonic.Buffer.upd\'"))) || (

let uu____7485 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7485 "LowStar.UninitializedBuffer.uupd"))) -> begin
(

let uu____7489 = (

let uu____7496 = (translate_expr env e1)
in (

let uu____7497 = (translate_expr env e2)
in (

let uu____7498 = (translate_expr env e3)
in ((uu____7496), (uu____7497), (uu____7498)))))
in EBufWrite (uu____7489))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7500; FStar_Extraction_ML_Syntax.loc = uu____7501}, uu____7502); FStar_Extraction_ML_Syntax.mlty = uu____7503; FStar_Extraction_ML_Syntax.loc = uu____7504}, (e1)::(e2)::[]) when (

let uu____7513 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7513 "FStar.HyperStack.ST.op_Colon_Equals")) -> begin
(

let uu____7517 = (

let uu____7524 = (translate_expr env e1)
in (

let uu____7525 = (translate_expr env e2)
in ((uu____7524), (EConstant (((UInt32), ("0")))), (uu____7525))))
in EBufWrite (uu____7517))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7529; FStar_Extraction_ML_Syntax.loc = uu____7530}, (uu____7531)::[]) when (

let uu____7534 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7534 "FStar.HyperStack.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7539; FStar_Extraction_ML_Syntax.loc = uu____7540}, (uu____7541)::[]) when (

let uu____7544 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7544 "FStar.HyperStack.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7549; FStar_Extraction_ML_Syntax.loc = uu____7550}, uu____7551); FStar_Extraction_ML_Syntax.mlty = uu____7552; FStar_Extraction_ML_Syntax.loc = uu____7553}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (((

let uu____7567 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7567 "FStar.Buffer.blit")) || (

let uu____7572 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7572 "LowStar.Monotonic.Buffer.blit"))) || (

let uu____7577 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7577 "LowStar.UninitializedBuffer.ublit"))) -> begin
(

let uu____7581 = (

let uu____7592 = (translate_expr env e1)
in (

let uu____7593 = (translate_expr env e2)
in (

let uu____7594 = (translate_expr env e3)
in (

let uu____7595 = (translate_expr env e4)
in (

let uu____7596 = (translate_expr env e5)
in ((uu____7592), (uu____7593), (uu____7594), (uu____7595), (uu____7596)))))))
in EBufBlit (uu____7581))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7598; FStar_Extraction_ML_Syntax.loc = uu____7599}, uu____7600); FStar_Extraction_ML_Syntax.mlty = uu____7601; FStar_Extraction_ML_Syntax.loc = uu____7602}, (e1)::(e2)::(e3)::[]) when (

let s = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in ((Prims.op_Equality s "FStar.Buffer.fill") || (Prims.op_Equality s "LowStar.Monotonic.Buffer.fill"))) -> begin
(

let uu____7618 = (

let uu____7625 = (translate_expr env e1)
in (

let uu____7626 = (translate_expr env e2)
in (

let uu____7627 = (translate_expr env e3)
in ((uu____7625), (uu____7626), (uu____7627)))))
in EBufFill (uu____7618))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7629; FStar_Extraction_ML_Syntax.loc = uu____7630}, (uu____7631)::[]) when (

let uu____7634 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7634 "FStar.HyperStack.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7639; FStar_Extraction_ML_Syntax.loc = uu____7640}, uu____7641); FStar_Extraction_ML_Syntax.mlty = uu____7642; FStar_Extraction_ML_Syntax.loc = uu____7643}, (_ebuf)::(_eseq)::[]) when ((((

let uu____7654 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7654 "LowStar.Monotonic.Buffer.witness_p")) || (

let uu____7659 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7659 "LowStar.Monotonic.Buffer.recall_p"))) || (

let uu____7664 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7664 "LowStar.ImmutableBuffer.witness_contents"))) || (

let uu____7669 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7669 "LowStar.ImmutableBuffer.recall_contents"))) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____7674; FStar_Extraction_ML_Syntax.loc = uu____7675}, (e1)::[]) when (

let uu____7679 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____7679 "Obj.repr")) -> begin
(

let uu____7683 = (

let uu____7688 = (translate_expr env e1)
in ((uu____7688), (TAny)))
in ECast (uu____7683))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____7691; FStar_Extraction_ML_Syntax.loc = uu____7692}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____7708 = (FStar_Util.must (mk_width m))
in (

let uu____7709 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____7708 uu____7709 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____7711; FStar_Extraction_ML_Syntax.loc = uu____7712}, args) when (is_bool_op op) -> begin
(

let uu____7726 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____7726 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____7728; FStar_Extraction_ML_Syntax.loc = uu____7729}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____7731; FStar_Extraction_ML_Syntax.loc = uu____7732})::[]) when (is_machine_int m) -> begin
(

let uu____7757 = (

let uu____7763 = (FStar_Util.must (mk_width m))
in ((uu____7763), (c)))
in EConstant (uu____7757))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____7766; FStar_Extraction_ML_Syntax.loc = uu____7767}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____7769; FStar_Extraction_ML_Syntax.loc = uu____7770})::[]) when (is_machine_int m) -> begin
(

let uu____7795 = (

let uu____7801 = (FStar_Util.must (mk_width m))
in ((uu____7801), (c)))
in EConstant (uu____7795))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____7803; FStar_Extraction_ML_Syntax.loc = uu____7804}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____7806; FStar_Extraction_ML_Syntax.loc = uu____7807})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____7820 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::("Compat")::("String")::[], "of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____7822; FStar_Extraction_ML_Syntax.loc = uu____7823}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____7825; FStar_Extraction_ML_Syntax.loc = uu____7826})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____7843 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::("String")::[], "of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____7845; FStar_Extraction_ML_Syntax.loc = uu____7846}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____7848; FStar_Extraction_ML_Syntax.loc = uu____7849})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____7864 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("LowStar")::("Literal")::[], "buffer_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____7866; FStar_Extraction_ML_Syntax.loc = uu____7867}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____7869; FStar_Extraction_ML_Syntax.loc = uu____7870})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
ECast (((EString (s)), (TBuf (TInt (UInt8)))))
end
| uu____7885 -> begin
(failwith "Cannot extract buffer_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____7888; FStar_Extraction_ML_Syntax.loc = uu____7889}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____7917 = (

let uu____7922 = (translate_expr env arg)
in ((uu____7922), (TInt (UInt64))))
in ECast (uu____7917))
end
| uu____7923 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____7927 = (

let uu____7932 = (translate_expr env arg)
in ((uu____7932), (TInt (UInt32))))
in ECast (uu____7927))
end
| uu____7933 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____7937 = (

let uu____7942 = (translate_expr env arg)
in ((uu____7942), (TInt (UInt16))))
in ECast (uu____7937))
end
| uu____7943 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____7947 = (

let uu____7952 = (translate_expr env arg)
in ((uu____7952), (TInt (UInt8))))
in ECast (uu____7947))
end
| uu____7953 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____7957 = (

let uu____7962 = (translate_expr env arg)
in ((uu____7962), (TInt (Int64))))
in ECast (uu____7957))
end
| uu____7963 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____7967 = (

let uu____7972 = (translate_expr env arg)
in ((uu____7972), (TInt (Int32))))
in ECast (uu____7967))
end
| uu____7973 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____7977 = (

let uu____7982 = (translate_expr env arg)
in ((uu____7982), (TInt (Int16))))
in ECast (uu____7977))
end
| uu____7983 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____7987 = (

let uu____7992 = (translate_expr env arg)
in ((uu____7992), (TInt (Int8))))
in ECast (uu____7987))
end
| uu____7993 -> begin
(

let uu____7995 = (

let uu____8002 = (

let uu____8005 = (translate_expr env arg)
in (uu____8005)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____8002)))
in EApp (uu____7995))
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

let uu____8025 = (

let uu____8032 = (translate_expr env head1)
in (

let uu____8033 = (FStar_List.map (translate_expr env) args)
in ((uu____8032), (uu____8033))))
in EApp (uu____8025))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(

let uu____8044 = (

let uu____8051 = (translate_expr env head1)
in (

let uu____8052 = (FStar_List.map (translate_type env) ty_args)
in ((uu____8051), (uu____8052))))
in ETypApp (uu____8044))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) -> begin
(

let uu____8060 = (

let uu____8065 = (translate_expr env e1)
in (

let uu____8066 = (translate_type env t_to)
in ((uu____8065), (uu____8066))))
in ECast (uu____8060))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____8067, fields) -> begin
(

let uu____8089 = (

let uu____8101 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____8102 = (FStar_List.map (fun uu____8124 -> (match (uu____8124) with
| (field, expr) -> begin
(

let uu____8139 = (translate_expr env expr)
in ((field), (uu____8139)))
end)) fields)
in ((uu____8101), (uu____8102))))
in EFlat (uu____8089))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) -> begin
(

let uu____8150 = (

let uu____8158 = (assert_lid env e1.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____8159 = (translate_expr env e1)
in ((uu____8158), (uu____8159), ((FStar_Pervasives_Native.snd path)))))
in EField (uu____8150))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____8165) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, uu____8178) -> begin
(

let uu____8183 = (

let uu____8185 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head1)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____8185))
in (failwith uu____8183))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____8197 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____8197))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____8203 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____8203))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8206, cons1), es) -> begin
(

let uu____8221 = (

let uu____8231 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____8232 = (FStar_List.map (translate_expr env) es)
in ((uu____8231), (cons1), (uu____8232))))
in ECons (uu____8221))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env1 = (add_binders env args)
in (

let uu____8258 = (

let uu____8267 = (translate_expr env1 body)
in (

let uu____8268 = (translate_type env1 body.FStar_Extraction_ML_Syntax.mlty)
in ((binders), (uu____8267), (uu____8268))))
in EFun (uu____8258))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____8278 = (

let uu____8285 = (translate_expr env e1)
in (

let uu____8286 = (translate_expr env e2)
in (

let uu____8287 = (match (e3) with
| FStar_Pervasives_Native.None -> begin
EUnit
end
| FStar_Pervasives_Native.Some (e31) -> begin
(translate_expr env e31)
end)
in ((uu____8285), (uu____8286), (uu____8287)))))
in EIfThenElse (uu____8278))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____8289) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____8297) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____8313) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____8331 = (

let uu____8346 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____8346)))
in TApp (uu____8331))
end
| uu____8359 -> begin
TQualified (lid)
end)
end
| uu____8361 -> begin
(

let uu____8362 = (

let uu____8364 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.format1 "invalid argument: expected MLTY_Named, got %s" uu____8364))
in (failwith uu____8362))
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____8398 -> (match (uu____8398) with
| (pat, guard, expr) -> begin
(match ((Prims.op_Equality guard FStar_Pervasives_Native.None)) with
| true -> begin
(

let uu____8425 = (translate_pat env pat)
in (match (uu____8425) with
| (env1, pat1) -> begin
(

let uu____8436 = (translate_expr env1 expr)
in ((pat1), (uu____8436)))
end))
end
| uu____8437 -> begin
(failwith "todo: translate_branch")
end)
end))
and translate_width : (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option  ->  width = (fun uu___7_8444 -> (match (uu___7_8444) with
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

let uu____8511 = (

let uu____8512 = (

let uu____8518 = (translate_width sw)
in ((uu____8518), (s)))
in PConstant (uu____8512))
in ((env), (uu____8511)))
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
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8528, cons1), ps) -> begin
(

let uu____8543 = (FStar_List.fold_left (fun uu____8563 p1 -> (match (uu____8563) with
| (env1, acc) -> begin
(

let uu____8583 = (translate_pat env1 p1)
in (match (uu____8583) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____8543) with
| (env1, ps1) -> begin
((env1), (PCons (((cons1), ((FStar_List.rev ps1))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____8613, ps) -> begin
(

let uu____8635 = (FStar_List.fold_left (fun uu____8672 uu____8673 -> (match (((uu____8672), (uu____8673))) with
| ((env1, acc), (field, p1)) -> begin
(

let uu____8753 = (translate_pat env1 p1)
in (match (uu____8753) with
| (env2, p2) -> begin
((env2), ((((field), (p2)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____8635) with
| (env1, ps1) -> begin
((env1), (PRecord ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____8824 = (FStar_List.fold_left (fun uu____8844 p1 -> (match (uu____8844) with
| (env1, acc) -> begin
(

let uu____8864 = (translate_pat env1 p1)
in (match (uu____8864) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____8824) with
| (env1, ps1) -> begin
((env1), (PTuple ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____8891) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____8897) -> begin
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

let uu____8911 = (

let uu____8913 = (FStar_String.list_of_string s)
in (FStar_All.pipe_right uu____8913 (FStar_Util.for_some (fun c1 -> (Prims.op_Equality c1 (FStar_Char.char_of_int (Prims.parse_int "0")))))))
in (match (uu____8911) with
| true -> begin
(

let uu____8928 = (FStar_Util.format1 "Refusing to translate a string literal that contains a null character: %s" s)
in (failwith uu____8928))
end
| uu____8931 -> begin
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
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____8955)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____8973) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____8975) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) -> begin
EConstant (((CInt), (s)))
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____8999 = (

let uu____9006 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____9006)))
in EApp (uu____8999)))




