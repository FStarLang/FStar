
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
| uu____641 -> begin
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
| uu____735 -> begin
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
| uu____843 -> begin
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
| uu____931 -> begin
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
| uu____1041 -> begin
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
| uu____1141 -> begin
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
| uu____1257 -> begin
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
| uu____1288 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____1294 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____1300 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1306 -> begin
false
end))


let uu___is_WipeBody : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WipeBody -> begin
true
end
| uu____1312 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1318 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1324 -> begin
false
end))


let uu___is_GCType : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GCType -> begin
true
end
| uu____1330 -> begin
false
end))


let uu___is_Comment : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____1337 -> begin
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
| uu____1350 -> begin
false
end))


let uu___is_Const : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____1357 -> begin
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
| uu____1371 -> begin
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
| uu____1385 -> begin
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
| uu____1398 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____1404 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____1410 -> begin
false
end))


let uu___is_ManuallyManaged : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ManuallyManaged -> begin
true
end
| uu____1416 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____1423 -> begin
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
| uu____1443 -> begin
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
| uu____1479 -> begin
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
| uu____1504 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____1517 -> begin
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
| uu____1555 -> begin
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
| uu____1593 -> begin
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
| uu____1631 -> begin
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
| uu____1665 -> begin
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
| uu____1689 -> begin
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
| uu____1721 -> begin
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
| uu____1757 -> begin
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
| uu____1789 -> begin
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
| uu____1825 -> begin
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
| uu____1861 -> begin
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
| uu____1915 -> begin
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
| uu____1963 -> begin
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
| uu____1993 -> begin
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
| uu____2018 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____2024 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____2031 -> begin
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
| uu____2044 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____2050 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____2057 -> begin
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
| uu____2081 -> begin
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
| uu____2131 -> begin
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
| uu____2167 -> begin
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
| uu____2199 -> begin
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
| uu____2233 -> begin
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
| uu____2261 -> begin
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
| uu____2305 -> begin
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
| uu____2337 -> begin
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
| uu____2359 -> begin
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
| uu____2397 -> begin
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
| uu____2411 -> begin
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
| uu____2429 -> begin
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
| uu____2454 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____2460 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____2466 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____2472 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____2478 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____2484 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____2490 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____2496 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____2502 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____2508 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____2514 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____2520 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____2526 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____2532 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____2538 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____2544 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____2550 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____2556 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____2562 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____2568 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____2574 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____2580 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____2586 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____2592 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____2598 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____2604 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____2611 -> begin
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
| uu____2625 -> begin
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
| uu____2645 -> begin
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
| uu____2679 -> begin
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
| uu____2705 -> begin
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
| uu____2741 -> begin
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
| uu____2766 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____2772 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____2778 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____2784 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____2790 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____2796 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____2802 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____2808 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____2814 -> begin
false
end))


let uu___is_CInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInt -> begin
true
end
| uu____2820 -> begin
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
| uu____2851 -> begin
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
| uu____2865 -> begin
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
| uu____2878 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____2891 -> begin
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
| uu____2922 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____2928 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____2939 -> begin
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
| uu____2965 -> begin
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
| uu____2991 -> begin
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
| uu____3043 -> begin
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


let fst3 : 'Auu____3123 'Auu____3124 'Auu____3125 . ('Auu____3123 * 'Auu____3124 * 'Auu____3125)  ->  'Auu____3123 = (fun uu____3136 -> (match (uu____3136) with
| (x, uu____3144, uu____3145) -> begin
x
end))


let snd3 : 'Auu____3154 'Auu____3155 'Auu____3156 . ('Auu____3154 * 'Auu____3155 * 'Auu____3156)  ->  'Auu____3155 = (fun uu____3167 -> (match (uu____3167) with
| (uu____3174, x, uu____3176) -> begin
x
end))


let thd3 : 'Auu____3185 'Auu____3186 'Auu____3187 . ('Auu____3185 * 'Auu____3186 * 'Auu____3187)  ->  'Auu____3187 = (fun uu____3198 -> (match (uu____3198) with
| (uu____3205, uu____3206, x) -> begin
x
end))


let mk_width : Prims.string  ->  width FStar_Pervasives_Native.option = (fun uu___281_3214 -> (match (uu___281_3214) with
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
| uu____3217 -> begin
FStar_Pervasives_Native.None
end))


let mk_bool_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___282_3224 -> (match (uu___282_3224) with
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
| uu____3227 -> begin
FStar_Pervasives_Native.None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> (Prims.op_disEquality (mk_bool_op op) FStar_Pervasives_Native.None))


let mk_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___283_3241 -> (match (uu___283_3241) with
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
| uu____3244 -> begin
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

let uu___289_3364 = env
in {names = ({pretty = x})::env.names; names_t = uu___289_3364.names_t; module_name = uu___289_3364.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___290_3375 = env
in {names = uu___290_3375.names; names_t = (x)::env.names_t; module_name = uu___290_3375.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____3386 = (FStar_List.tryFind (fun name -> (Prims.op_Equality name.pretty x)) env.names)
in (match (uu____3386) with
| FStar_Pervasives_Native.Some (name) -> begin
name
end
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: name not found")
end)))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_All.try_with (fun uu___292_3403 -> (match (()) with
| () -> begin
(FStar_List.index (fun name -> (Prims.op_Equality name.pretty x)) env.names)
end)) (fun uu___291_3408 -> (

let uu____3409 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____3409)))))


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_All.try_with (fun uu___294_3421 -> (match (()) with
| () -> begin
(FStar_List.index (fun name -> (Prims.op_Equality name x)) env.names_t)
end)) (fun uu___293_3426 -> (

let uu____3427 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____3427)))))


let add_binders : 'Auu____3434 . env  ->  (Prims.string * 'Auu____3434) Prims.list  ->  env = (fun env binders -> (FStar_List.fold_left (fun env1 uu____3466 -> (match (uu____3466) with
| (name, uu____3472) -> begin
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
| uu____3509 -> begin
(failwith "Argument of FStar.Buffer.createL is not a list literal!")
end))
in (list_elements [] e2)))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____3724 -> (match (uu____3724) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____3772 = m
in (match (uu____3772) with
| (path, uu____3786, uu____3787) -> begin
(FStar_Extraction_ML_Syntax.string_of_mlpath path)
end))
in (FStar_All.try_with (fun uu___296_3805 -> (match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
(

let uu____3809 = (translate_module m)
in FStar_Pervasives_Native.Some (uu____3809));
)
end)) (fun uu___295_3813 -> (match (uu___295_3813) with
| e -> begin
((

let uu____3818 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____3818));
FStar_Pervasives_Native.None;
)
end))))) modules)
end))
and translate_module : (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____3819 -> (match (uu____3819) with
| (module_name, modul, uu____3834) -> begin
(

let module_name1 = (FStar_List.append (FStar_Pervasives_Native.fst module_name) (((FStar_Pervasives_Native.snd module_name))::[]))
in (

let program = (match (modul) with
| FStar_Pervasives_Native.Some (_signature, decls) -> begin
(FStar_List.collect (translate_decl (empty module_name1)) decls)
end
| uu____3861 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name1)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.meta Prims.list  ->  flag Prims.list = (fun flags1 -> (FStar_List.choose (fun uu___284_3872 -> (match (uu___284_3872) with
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
| uu____3879 -> begin
FStar_Pervasives_Native.None
end)) flags1))
and translate_cc : FStar_Extraction_ML_Syntax.meta Prims.list  ->  cc FStar_Pervasives_Native.option = (fun flags1 -> (

let uu____3883 = (FStar_List.choose (fun uu___285_3888 -> (match (uu___285_3888) with
| FStar_Extraction_ML_Syntax.CCConv (s) -> begin
FStar_Pervasives_Native.Some (s)
end
| uu____3892 -> begin
FStar_Pervasives_Native.None
end)) flags1)
in (match (uu____3883) with
| ("stdcall")::[] -> begin
FStar_Pervasives_Native.Some (StdCall)
end
| ("fastcall")::[] -> begin
FStar_Pervasives_Native.Some (FastCall)
end
| ("cdecl")::[] -> begin
FStar_Pervasives_Native.Some (CDecl)
end
| uu____3895 -> begin
FStar_Pervasives_Native.None
end)))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.list = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) -> begin
(FStar_List.choose (translate_let env flavor) lbs)
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____3908) -> begin
[]
end
| FStar_Extraction_ML_Syntax.MLM_Ty (tys) -> begin
(FStar_List.choose (translate_type_decl env) tys)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____3910) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____3914) -> begin
((FStar_Util.print1_warning "Not extracting exception %s to KreMLin (exceptions unsupported)\n" m);
[];
)
end))
and translate_let : env  ->  FStar_Extraction_ML_Syntax.mlletflavor  ->  FStar_Extraction_ML_Syntax.mllb  ->  decl FStar_Pervasives_Native.option = (fun env flavor lb -> (match (lb) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3936; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____3939; FStar_Extraction_ML_Syntax.loc = uu____3940}; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____3942} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3957 -> begin
(

let assumed = (FStar_Util.for_some (fun uu___286_3960 -> (match (uu___286_3960) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____3961 -> begin
false
end)) meta)
in (

let env1 = (match ((Prims.op_Equality flavor FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name)
end
| uu____3963 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 name1 -> (extend_t env2 name1)) env1 tvars)
in (

let rec find_return_type = (fun eff i uu___287_3990 -> (match (uu___287_3990) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3997, eff1, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type eff1 (i - (Prims.parse_int "1")) t)
end
| t -> begin
((i), (eff), (t))
end))
in (

let name1 = ((env2.module_name), (name))
in (

let uu____4010 = (find_return_type FStar_Extraction_ML_Syntax.E_PURE (FStar_List.length args) t0)
in (match (uu____4010) with
| (i, eff, t) -> begin
((match ((i > (Prims.parse_int "0"))) with
| true -> begin
(

let msg = "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
in (

let uu____4028 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print2_warning "Not extracting %s to KreMLin (%s)\n" uu____4028 msg)))
end
| uu____4029 -> begin
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
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____4043) -> begin
(

let uu____4044 = (translate_flags meta)
in (MustDisappear)::uu____4044)
end
| (FStar_Extraction_ML_Syntax.E_PURE, TUnit) -> begin
(

let uu____4047 = (translate_flags meta)
in (MustDisappear)::uu____4047)
end
| uu____4050 -> begin
(translate_flags meta)
end)
in (match (assumed) with
| true -> begin
(match ((Prims.op_Equality (FStar_List.length tvars) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4059 = (

let uu____4060 = (

let uu____4079 = (translate_type env3 t0)
in ((cc), (meta1), (name1), (uu____4079)))
in DExternal (uu____4060))
in FStar_Pervasives_Native.Some (uu____4059))
end
| uu____4090 -> begin
((

let uu____4092 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print1_warning "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n" uu____4092));
FStar_Pervasives_Native.None;
)
end)
end
| uu____4093 -> begin
(FStar_All.try_with (fun uu___298_4098 -> (match (()) with
| () -> begin
(

let body1 = (translate_expr env3 body)
in FStar_Pervasives_Native.Some (DFunction (((cc), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (body1)))))
end)) (fun uu___297_4119 -> (match (uu___297_4119) with
| e -> begin
(

let msg = (FStar_Util.print_exn e)
in ((

let uu____4125 = (

let uu____4130 = (

let uu____4131 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.format2 "Error while extracting %s to KreMLin (%s)\n" uu____4131 msg))
in ((FStar_Errors.Warning_FunctionNotExtacted), (uu____4130)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4125));
(

let msg1 = (Prims.strcat "This function was not extracted:\n" msg)
in FStar_Pervasives_Native.Some (DFunction (((cc), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (EAbortS (msg1))))));
))
end)))
end))))));
)
end)))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4148; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____4151; FStar_Extraction_ML_Syntax.loc = uu____4152}, uu____4153, uu____4154); FStar_Extraction_ML_Syntax.mlty = uu____4155; FStar_Extraction_ML_Syntax.loc = uu____4156}; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____4158} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4173 -> begin
(

let assumed = (FStar_Util.for_some (fun uu___286_4176 -> (match (uu___286_4176) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____4177 -> begin
false
end)) meta)
in (

let env1 = (match ((Prims.op_Equality flavor FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name)
end
| uu____4179 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 name1 -> (extend_t env2 name1)) env1 tvars)
in (

let rec find_return_type = (fun eff i uu___287_4206 -> (match (uu___287_4206) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4213, eff1, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type eff1 (i - (Prims.parse_int "1")) t)
end
| t -> begin
((i), (eff), (t))
end))
in (

let name1 = ((env2.module_name), (name))
in (

let uu____4226 = (find_return_type FStar_Extraction_ML_Syntax.E_PURE (FStar_List.length args) t0)
in (match (uu____4226) with
| (i, eff, t) -> begin
((match ((i > (Prims.parse_int "0"))) with
| true -> begin
(

let msg = "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
in (

let uu____4244 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print2_warning "Not extracting %s to KreMLin (%s)\n" uu____4244 msg)))
end
| uu____4245 -> begin
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
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____4259) -> begin
(

let uu____4260 = (translate_flags meta)
in (MustDisappear)::uu____4260)
end
| (FStar_Extraction_ML_Syntax.E_PURE, TUnit) -> begin
(

let uu____4263 = (translate_flags meta)
in (MustDisappear)::uu____4263)
end
| uu____4266 -> begin
(translate_flags meta)
end)
in (match (assumed) with
| true -> begin
(match ((Prims.op_Equality (FStar_List.length tvars) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4275 = (

let uu____4276 = (

let uu____4295 = (translate_type env3 t0)
in ((cc), (meta1), (name1), (uu____4295)))
in DExternal (uu____4276))
in FStar_Pervasives_Native.Some (uu____4275))
end
| uu____4306 -> begin
((

let uu____4308 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print1_warning "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n" uu____4308));
FStar_Pervasives_Native.None;
)
end)
end
| uu____4309 -> begin
(FStar_All.try_with (fun uu___298_4314 -> (match (()) with
| () -> begin
(

let body1 = (translate_expr env3 body)
in FStar_Pervasives_Native.Some (DFunction (((cc), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (body1)))))
end)) (fun uu___297_4335 -> (match (uu___297_4335) with
| e -> begin
(

let msg = (FStar_Util.print_exn e)
in ((

let uu____4341 = (

let uu____4346 = (

let uu____4347 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.format2 "Error while extracting %s to KreMLin (%s)\n" uu____4347 msg))
in ((FStar_Errors.Warning_FunctionNotExtacted), (uu____4346)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4341));
(

let msg1 = (Prims.strcat "This function was not extracted:\n" msg)
in FStar_Pervasives_Native.Some (DFunction (((cc), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (EAbortS (msg1))))));
))
end)))
end))))));
)
end)))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4364; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____4367} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4370 -> begin
(

let meta1 = (translate_flags meta)
in (

let env1 = (FStar_List.fold_left (fun env1 name1 -> (extend_t env1 name1)) env tvars)
in (

let t1 = (translate_type env1 t)
in (

let name1 = ((env1.module_name), (name))
in (FStar_All.try_with (fun uu___300_4393 -> (match (()) with
| () -> begin
(

let expr1 = (translate_expr env1 expr)
in FStar_Pervasives_Native.Some (DGlobal (((meta1), (name1), ((FStar_List.length tvars)), (t1), (expr1)))))
end)) (fun uu___299_4408 -> (match (uu___299_4408) with
| e -> begin
((

let uu____4413 = (

let uu____4418 = (

let uu____4419 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (

let uu____4420 = (FStar_Util.print_exn e)
in (FStar_Util.format2 "Error extracting %s to KreMLin (%s)\n" uu____4419 uu____4420)))
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____4418)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4413));
FStar_Pervasives_Native.Some (DGlobal (((meta1), (name1), ((FStar_List.length tvars)), (t1), (EAny))));
)
end)))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4431; FStar_Extraction_ML_Syntax.mllb_def = uu____4432; FStar_Extraction_ML_Syntax.mllb_meta = uu____4433; FStar_Extraction_ML_Syntax.print_typ = uu____4434} -> begin
((

let uu____4438 = (

let uu____4443 = (FStar_Util.format1 "Not extracting %s to KreMLin\n" name)
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____4443)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4438));
(match (ts) with
| FStar_Pervasives_Native.Some (idents, t) -> begin
(

let uu____4447 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" (FStar_String.concat ", " idents) uu____4447))
end
| FStar_Pervasives_Native.None -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
and translate_type_decl : env  ->  FStar_Extraction_ML_Syntax.one_mltydecl  ->  decl FStar_Pervasives_Native.option = (fun env ty -> (

let uu____4454 = ty
in (match (uu____4454) with
| (uu____4457, uu____4458, uu____4459, uu____4460, flags1, uu____4462) -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags1)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4473 -> begin
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
| uu____4504 -> begin
(match (assumed) with
| true -> begin
(

let name2 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in ((FStar_Util.print1_warning "Not extracting type definition %s to KreMLin (assumed type)\n" name2);
FStar_Pervasives_Native.None;
))
end
| uu____4509 -> begin
(

let uu____4510 = (

let uu____4511 = (

let uu____4528 = (translate_flags flags2)
in (

let uu____4531 = (translate_type env1 t)
in ((name1), (uu____4528), ((FStar_List.length args)), (uu____4531))))
in DTypeAlias (uu____4511))
in FStar_Pervasives_Native.Some (uu____4510))
end)
end)))
end
| (uu____4540, name, _mangled_name, args, flags2, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 name2 -> (extend_t env1 name2)) env args)
in (

let uu____4572 = (

let uu____4573 = (

let uu____4600 = (translate_flags flags2)
in (

let uu____4603 = (FStar_List.map (fun uu____4630 -> (match (uu____4630) with
| (f, t) -> begin
(

let uu____4645 = (

let uu____4650 = (translate_type env1 t)
in ((uu____4650), (false)))
in ((f), (uu____4645)))
end)) fields)
in ((name1), (uu____4600), ((FStar_List.length args)), (uu____4603))))
in DTypeFlat (uu____4573))
in FStar_Pervasives_Native.Some (uu____4572))))
end
| (uu____4673, name, _mangled_name, args, flags2, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let flags3 = (translate_flags flags2)
in (

let env1 = (FStar_List.fold_left extend_t env args)
in (

let uu____4710 = (

let uu____4711 = (

let uu____4744 = (FStar_List.map (fun uu____4789 -> (match (uu____4789) with
| (cons1, ts) -> begin
(

let uu____4828 = (FStar_List.map (fun uu____4855 -> (match (uu____4855) with
| (name2, t) -> begin
(

let uu____4870 = (

let uu____4875 = (translate_type env1 t)
in ((uu____4875), (false)))
in ((name2), (uu____4870)))
end)) ts)
in ((cons1), (uu____4828)))
end)) branches)
in ((name1), (flags3), ((FStar_List.length args)), (uu____4744)))
in DTypeVariant (uu____4711))
in FStar_Pervasives_Native.Some (uu____4710)))))
end
| (uu____4914, name, _mangled_name, uu____4917, uu____4918, uu____4919) -> begin
((

let uu____4929 = (

let uu____4934 = (FStar_Util.format1 "Error extracting type definition %s to KreMLin\n" name)
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____4934)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4929));
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

let uu____4938 = (find_t env name)
in TBound (uu____4938))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____4940, t2) -> begin
(

let uu____4942 = (

let uu____4947 = (translate_type env t1)
in (

let uu____4948 = (translate_type env t2)
in ((uu____4947), (uu____4948))))
in TArrow (uu____4942))
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____4952 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4952 "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____4956 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4956 "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____4962 = (FStar_Util.must (mk_width m))
in TInt (uu____4962))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____4968 = (FStar_Util.must (mk_width m))
in TInt (uu____4968))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____4973 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4973 "FStar.Monotonic.HyperStack.mem")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____4974)::(arg)::(uu____4976)::[], p) when ((((

let uu____4982 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4982 "FStar.Monotonic.HyperStack.s_mref")) || (

let uu____4984 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4984 "FStar.Monotonic.HyperHeap.mrref"))) || (

let uu____4986 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4986 "FStar.HyperStack.ST.m_rref"))) || (

let uu____4988 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4988 "FStar.HyperStack.ST.s_mref"))) -> begin
(

let uu____4989 = (translate_type env arg)
in TBuf (uu____4989))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::(uu____4991)::[], p) when (((((((((((

let uu____4997 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4997 "FStar.Monotonic.HyperStack.mreference")) || (

let uu____4999 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4999 "FStar.Monotonic.HyperStack.mstackref"))) || (

let uu____5001 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5001 "FStar.Monotonic.HyperStack.mref"))) || (

let uu____5003 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5003 "FStar.Monotonic.HyperStack.mmmstackref"))) || (

let uu____5005 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5005 "FStar.Monotonic.HyperStack.mmmref"))) || (

let uu____5007 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5007 "FStar.Monotonic.Heap.mref"))) || (

let uu____5009 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5009 "FStar.HyperStack.ST.mreference"))) || (

let uu____5011 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5011 "FStar.HyperStack.ST.mstackref"))) || (

let uu____5013 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5013 "FStar.HyperStack.ST.mref"))) || (

let uu____5015 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5015 "FStar.HyperStack.ST.mmmstackref"))) || (

let uu____5017 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5017 "FStar.HyperStack.ST.mmmref"))) -> begin
(

let uu____5018 = (translate_type env arg)
in TBuf (uu____5018))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::(uu____5020)::(uu____5021)::[], p) when (

let uu____5025 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5025 "LowStar.Monotonic.Buffer.mbuffer")) -> begin
(

let uu____5026 = (translate_type env arg)
in TBuf (uu____5026))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((((((((((((((

let uu____5033 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5033 "FStar.Buffer.buffer")) || (

let uu____5035 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5035 "LowStar.Buffer.buffer"))) || (

let uu____5037 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5037 "LowStar.ImmutableBuffer.ibuffer"))) || (

let uu____5039 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5039 "LowStar.UninitializedBuffer.ubuffer"))) || (

let uu____5041 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5041 "FStar.HyperStack.reference"))) || (

let uu____5043 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5043 "FStar.HyperStack.stackref"))) || (

let uu____5045 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5045 "FStar.HyperStack.ref"))) || (

let uu____5047 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5047 "FStar.HyperStack.mmstackref"))) || (

let uu____5049 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5049 "FStar.HyperStack.mmref"))) || (

let uu____5051 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5051 "FStar.HyperStack.ST.reference"))) || (

let uu____5053 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5053 "FStar.HyperStack.ST.stackref"))) || (

let uu____5055 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5055 "FStar.HyperStack.ST.ref"))) || (

let uu____5057 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5057 "FStar.HyperStack.ST.mmstackref"))) || (

let uu____5059 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5059 "FStar.HyperStack.ST.mmref"))) -> begin
(

let uu____5060 = (translate_type env arg)
in TBuf (uu____5060))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____5061)::(arg)::[], p) when ((

let uu____5068 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5068 "FStar.HyperStack.s_ref")) || (

let uu____5070 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5070 "FStar.HyperStack.ST.s_ref"))) -> begin
(

let uu____5071 = (translate_type env arg)
in TBuf (uu____5071))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____5072)::[], p) when (

let uu____5076 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5076 "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when (((Prims.op_Equality ns (("Prims")::[])) || (Prims.op_Equality ns (("FStar")::("Pervasives")::("Native")::[]))) && (FStar_Util.starts_with t1 "tuple")) -> begin
(

let uu____5102 = (FStar_List.map (translate_type env) args)
in TTuple (uu____5102))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5111 = (

let uu____5124 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____5124)))
in TApp (uu____5111))
end
| uu____5135 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____5139 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____5139))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____5155 -> (match (uu____5155) with
| (name, typ) -> begin
(

let uu____5162 = (translate_type env typ)
in {name = name; typ = uu____5162; mut = false})
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

let uu____5167 = (find env name)
in EBound (uu____5167))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____5172 = (

let uu____5177 = (FStar_Util.must (mk_op op))
in (

let uu____5178 = (FStar_Util.must (mk_width m))
in ((uu____5177), (uu____5178))))
in EOp (uu____5172))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____5182 = (

let uu____5187 = (FStar_Util.must (mk_bool_op op))
in ((uu____5187), (Bool)))
in EOp (uu____5182))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n1) -> begin
EQualified (n1)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.mllb_meta = flags1; FStar_Extraction_ML_Syntax.print_typ = print7})::[]), continuation) -> begin
(

let binder = (

let uu____5206 = (translate_type env typ)
in {name = name; typ = uu____5206; mut = false})
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

let uu____5232 = (

let uu____5243 = (translate_expr env expr)
in (

let uu____5244 = (translate_branches env branches)
in ((uu____5243), (uu____5244))))
in EMatch (uu____5232))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5258; FStar_Extraction_ML_Syntax.loc = uu____5259}, (t)::[]); FStar_Extraction_ML_Syntax.mlty = uu____5261; FStar_Extraction_ML_Syntax.loc = uu____5262}, (arg)::[]) when (

let uu____5268 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5268 "FStar.Dyn.undyn")) -> begin
(

let uu____5269 = (

let uu____5274 = (translate_expr env arg)
in (

let uu____5275 = (translate_type env t)
in ((uu____5274), (uu____5275))))
in ECast (uu____5269))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5277; FStar_Extraction_ML_Syntax.loc = uu____5278}, uu____5279); FStar_Extraction_ML_Syntax.mlty = uu____5280; FStar_Extraction_ML_Syntax.loc = uu____5281}, uu____5282) when (

let uu____5291 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5291 "Prims.admit")) -> begin
EAbort
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5293; FStar_Extraction_ML_Syntax.loc = uu____5294}, uu____5295); FStar_Extraction_ML_Syntax.mlty = uu____5296; FStar_Extraction_ML_Syntax.loc = uu____5297}, (arg)::[]) when (((

let uu____5307 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5307 "FStar.HyperStack.All.failwith")) || (

let uu____5309 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5309 "FStar.Error.unexpected"))) || (

let uu____5311 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5311 "FStar.Error.unreachable"))) -> begin
(match (arg) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (msg)); FStar_Extraction_ML_Syntax.mlty = uu____5313; FStar_Extraction_ML_Syntax.loc = uu____5314} -> begin
EAbortS (msg)
end
| uu____5315 -> begin
(

let print7 = (

let uu____5317 = (

let uu____5318 = (

let uu____5319 = (FStar_Ident.lid_of_str "FStar.HyperStack.IO.print_string")
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5319))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____5318))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____5317))
in (

let print8 = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top (FStar_Extraction_ML_Syntax.MLE_App (((print7), ((arg)::[])))))
in (

let t = (translate_expr env print8)
in ESequence ((t)::(EAbort)::[]))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5325; FStar_Extraction_ML_Syntax.loc = uu____5326}, uu____5327); FStar_Extraction_ML_Syntax.mlty = uu____5328; FStar_Extraction_ML_Syntax.loc = uu____5329}, (e1)::[]) when ((

let uu____5339 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5339 "LowStar.ToFStarBuffer.new_to_old_st")) || (

let uu____5341 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5341 "LowStar.ToFStarBuffer.old_to_new_st"))) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5343; FStar_Extraction_ML_Syntax.loc = uu____5344}, uu____5345); FStar_Extraction_ML_Syntax.mlty = uu____5346; FStar_Extraction_ML_Syntax.loc = uu____5347}, (e1)::(e2)::[]) when ((((

let uu____5358 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5358 "FStar.Buffer.index")) || (

let uu____5360 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5360 "FStar.Buffer.op_Array_Access"))) || (

let uu____5362 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5362 "LowStar.Monotonic.Buffer.index"))) || (

let uu____5364 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5364 "LowStar.UninitializedBuffer.uindex"))) -> begin
(

let uu____5365 = (

let uu____5370 = (translate_expr env e1)
in (

let uu____5371 = (translate_expr env e2)
in ((uu____5370), (uu____5371))))
in EBufRead (uu____5365))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5373; FStar_Extraction_ML_Syntax.loc = uu____5374}, uu____5375); FStar_Extraction_ML_Syntax.mlty = uu____5376; FStar_Extraction_ML_Syntax.loc = uu____5377}, (e1)::[]) when (

let uu____5385 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5385 "FStar.HyperStack.ST.op_Bang")) -> begin
(

let uu____5386 = (

let uu____5391 = (translate_expr env e1)
in ((uu____5391), (EConstant (((UInt32), ("0"))))))
in EBufRead (uu____5386))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5393; FStar_Extraction_ML_Syntax.loc = uu____5394}, uu____5395); FStar_Extraction_ML_Syntax.mlty = uu____5396; FStar_Extraction_ML_Syntax.loc = uu____5397}, (e1)::(e2)::[]) when (((

let uu____5408 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5408 "FStar.Buffer.create")) || (

let uu____5410 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5410 "LowStar.Monotonic.Buffer.malloca"))) || (

let uu____5412 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5412 "LowStar.ImmutableBuffer.ialloca"))) -> begin
(

let uu____5413 = (

let uu____5420 = (translate_expr env e1)
in (

let uu____5421 = (translate_expr env e2)
in ((Stack), (uu____5420), (uu____5421))))
in EBufCreate (uu____5413))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5423; FStar_Extraction_ML_Syntax.loc = uu____5424}, uu____5425); FStar_Extraction_ML_Syntax.mlty = uu____5426; FStar_Extraction_ML_Syntax.loc = uu____5427}, (elen)::[]) when (

let uu____5435 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5435 "LowStar.UninitializedBuffer.ualloca")) -> begin
(

let uu____5436 = (

let uu____5441 = (translate_expr env elen)
in ((Stack), (uu____5441)))
in EBufCreateNoInit (uu____5436))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5443; FStar_Extraction_ML_Syntax.loc = uu____5444}, uu____5445); FStar_Extraction_ML_Syntax.mlty = uu____5446; FStar_Extraction_ML_Syntax.loc = uu____5447}, (init1)::[]) when (

let uu____5455 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5455 "FStar.HyperStack.ST.salloc")) -> begin
(

let uu____5456 = (

let uu____5463 = (translate_expr env init1)
in ((Stack), (uu____5463), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____5456))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5465; FStar_Extraction_ML_Syntax.loc = uu____5466}, uu____5467); FStar_Extraction_ML_Syntax.mlty = uu____5468; FStar_Extraction_ML_Syntax.loc = uu____5469}, (e2)::[]) when (((

let uu____5479 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5479 "FStar.Buffer.createL")) || (

let uu____5481 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5481 "LowStar.Monotonic.Buffer.malloca_of_list"))) || (

let uu____5483 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5483 "LowStar.ImmutableBuffer.ialloca_of_list"))) -> begin
(

let uu____5484 = (

let uu____5491 = (

let uu____5494 = (list_elements e2)
in (FStar_List.map (translate_expr env) uu____5494))
in ((Stack), (uu____5491)))
in EBufCreateL (uu____5484))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5500; FStar_Extraction_ML_Syntax.loc = uu____5501}, uu____5502); FStar_Extraction_ML_Syntax.mlty = uu____5503; FStar_Extraction_ML_Syntax.loc = uu____5504}, (_erid)::(e2)::[]) when ((

let uu____5515 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5515 "LowStar.Monotonic.Buffer.mgcmalloc_of_list")) || (

let uu____5517 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5517 "LowStar.ImmutableBuffer.igcmalloc_of_list"))) -> begin
(

let uu____5518 = (

let uu____5525 = (

let uu____5528 = (list_elements e2)
in (FStar_List.map (translate_expr env) uu____5528))
in ((Eternal), (uu____5525)))
in EBufCreateL (uu____5518))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5534; FStar_Extraction_ML_Syntax.loc = uu____5535}, uu____5536); FStar_Extraction_ML_Syntax.mlty = uu____5537; FStar_Extraction_ML_Syntax.loc = uu____5538}, (_rid)::(init1)::[]) when (

let uu____5547 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5547 "FStar.HyperStack.ST.ralloc")) -> begin
(

let uu____5548 = (

let uu____5555 = (translate_expr env init1)
in ((Eternal), (uu____5555), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____5548))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5557; FStar_Extraction_ML_Syntax.loc = uu____5558}, uu____5559); FStar_Extraction_ML_Syntax.mlty = uu____5560; FStar_Extraction_ML_Syntax.loc = uu____5561}, (_e0)::(e1)::(e2)::[]) when (((

let uu____5573 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5573 "FStar.Buffer.rcreate")) || (

let uu____5575 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5575 "LowStar.Monotonic.Buffer.mgcmalloc"))) || (

let uu____5577 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5577 "LowStar.ImmutableBuffer.igcmalloc"))) -> begin
(

let uu____5578 = (

let uu____5585 = (translate_expr env e1)
in (

let uu____5586 = (translate_expr env e2)
in ((Eternal), (uu____5585), (uu____5586))))
in EBufCreate (uu____5578))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5588; FStar_Extraction_ML_Syntax.loc = uu____5589}, uu____5590); FStar_Extraction_ML_Syntax.mlty = uu____5591; FStar_Extraction_ML_Syntax.loc = uu____5592}, (_erid)::(elen)::[]) when (

let uu____5601 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5601 "LowStar.UninitializedBuffer.ugcmalloc")) -> begin
(

let uu____5602 = (

let uu____5607 = (translate_expr env elen)
in ((Eternal), (uu____5607)))
in EBufCreateNoInit (uu____5602))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5609; FStar_Extraction_ML_Syntax.loc = uu____5610}, uu____5611); FStar_Extraction_ML_Syntax.mlty = uu____5612; FStar_Extraction_ML_Syntax.loc = uu____5613}, (_rid)::(init1)::[]) when (

let uu____5622 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5622 "FStar.HyperStack.ST.ralloc_mm")) -> begin
(

let uu____5623 = (

let uu____5630 = (translate_expr env init1)
in ((ManuallyManaged), (uu____5630), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____5623))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5632; FStar_Extraction_ML_Syntax.loc = uu____5633}, uu____5634); FStar_Extraction_ML_Syntax.mlty = uu____5635; FStar_Extraction_ML_Syntax.loc = uu____5636}, (_e0)::(e1)::(e2)::[]) when ((((

let uu____5648 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5648 "FStar.Buffer.rcreate_mm")) || (

let uu____5650 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5650 "LowStar.Monotonic.Buffer.mmalloc"))) || (

let uu____5652 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5652 "LowStar.Monotonic.Buffer.mmalloc"))) || (

let uu____5654 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5654 "LowStar.ImmutableBuffer.imalloc"))) -> begin
(

let uu____5655 = (

let uu____5662 = (translate_expr env e1)
in (

let uu____5663 = (translate_expr env e2)
in ((ManuallyManaged), (uu____5662), (uu____5663))))
in EBufCreate (uu____5655))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5665; FStar_Extraction_ML_Syntax.loc = uu____5666}, uu____5667); FStar_Extraction_ML_Syntax.mlty = uu____5668; FStar_Extraction_ML_Syntax.loc = uu____5669}, (_erid)::(elen)::[]) when (

let uu____5678 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5678 "LowStar.UninitializedBuffer.umalloc")) -> begin
(

let uu____5679 = (

let uu____5684 = (translate_expr env elen)
in ((ManuallyManaged), (uu____5684)))
in EBufCreateNoInit (uu____5679))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5686; FStar_Extraction_ML_Syntax.loc = uu____5687}, uu____5688); FStar_Extraction_ML_Syntax.mlty = uu____5689; FStar_Extraction_ML_Syntax.loc = uu____5690}, (e2)::[]) when (

let uu____5698 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5698 "FStar.HyperStack.ST.rfree")) -> begin
(

let uu____5699 = (translate_expr env e2)
in EBufFree (uu____5699))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5701; FStar_Extraction_ML_Syntax.loc = uu____5702}, uu____5703); FStar_Extraction_ML_Syntax.mlty = uu____5704; FStar_Extraction_ML_Syntax.loc = uu____5705}, (e2)::[]) when ((

let uu____5715 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5715 "FStar.Buffer.rfree")) || (

let uu____5717 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5717 "LowStar.Monotonic.Buffer.free"))) -> begin
(

let uu____5718 = (translate_expr env e2)
in EBufFree (uu____5718))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5720; FStar_Extraction_ML_Syntax.loc = uu____5721}, uu____5722); FStar_Extraction_ML_Syntax.mlty = uu____5723; FStar_Extraction_ML_Syntax.loc = uu____5724}, (e1)::(e2)::(_e3)::[]) when (

let uu____5734 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5734 "FStar.Buffer.sub")) -> begin
(

let uu____5735 = (

let uu____5740 = (translate_expr env e1)
in (

let uu____5741 = (translate_expr env e2)
in ((uu____5740), (uu____5741))))
in EBufSub (uu____5735))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5743; FStar_Extraction_ML_Syntax.loc = uu____5744}, uu____5745); FStar_Extraction_ML_Syntax.mlty = uu____5746; FStar_Extraction_ML_Syntax.loc = uu____5747}, (e1)::(e2)::(_e3)::[]) when (

let uu____5757 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5757 "LowStar.Monotonic.Buffer.msub")) -> begin
(

let uu____5758 = (

let uu____5763 = (translate_expr env e1)
in (

let uu____5764 = (translate_expr env e2)
in ((uu____5763), (uu____5764))))
in EBufSub (uu____5758))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5766; FStar_Extraction_ML_Syntax.loc = uu____5767}, uu____5768); FStar_Extraction_ML_Syntax.mlty = uu____5769; FStar_Extraction_ML_Syntax.loc = uu____5770}, (e1)::(e2)::[]) when (

let uu____5779 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5779 "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5781; FStar_Extraction_ML_Syntax.loc = uu____5782}, uu____5783); FStar_Extraction_ML_Syntax.mlty = uu____5784; FStar_Extraction_ML_Syntax.loc = uu____5785}, (e1)::(e2)::[]) when (

let uu____5794 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5794 "FStar.Buffer.offset")) -> begin
(

let uu____5795 = (

let uu____5800 = (translate_expr env e1)
in (

let uu____5801 = (translate_expr env e2)
in ((uu____5800), (uu____5801))))
in EBufSub (uu____5795))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5803; FStar_Extraction_ML_Syntax.loc = uu____5804}, uu____5805); FStar_Extraction_ML_Syntax.mlty = uu____5806; FStar_Extraction_ML_Syntax.loc = uu____5807}, (e1)::(e2)::[]) when (

let uu____5816 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5816 "LowStar.Monotonic.Buffer.moffset")) -> begin
(

let uu____5817 = (

let uu____5822 = (translate_expr env e1)
in (

let uu____5823 = (translate_expr env e2)
in ((uu____5822), (uu____5823))))
in EBufSub (uu____5817))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5825; FStar_Extraction_ML_Syntax.loc = uu____5826}, uu____5827); FStar_Extraction_ML_Syntax.mlty = uu____5828; FStar_Extraction_ML_Syntax.loc = uu____5829}, (e1)::(e2)::(e3)::[]) when ((((

let uu____5841 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5841 "FStar.Buffer.upd")) || (

let uu____5843 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5843 "FStar.Buffer.op_Array_Assignment"))) || (

let uu____5845 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5845 "LowStar.Monotonic.Buffer.upd\'"))) || (

let uu____5847 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5847 "LowStar.UninitializedBuffer.uupd"))) -> begin
(

let uu____5848 = (

let uu____5855 = (translate_expr env e1)
in (

let uu____5856 = (translate_expr env e2)
in (

let uu____5857 = (translate_expr env e3)
in ((uu____5855), (uu____5856), (uu____5857)))))
in EBufWrite (uu____5848))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5859; FStar_Extraction_ML_Syntax.loc = uu____5860}, uu____5861); FStar_Extraction_ML_Syntax.mlty = uu____5862; FStar_Extraction_ML_Syntax.loc = uu____5863}, (e1)::(e2)::[]) when (

let uu____5872 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5872 "FStar.HyperStack.ST.op_Colon_Equals")) -> begin
(

let uu____5873 = (

let uu____5880 = (translate_expr env e1)
in (

let uu____5881 = (translate_expr env e2)
in ((uu____5880), (EConstant (((UInt32), ("0")))), (uu____5881))))
in EBufWrite (uu____5873))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5883; FStar_Extraction_ML_Syntax.loc = uu____5884}, (uu____5885)::[]) when (

let uu____5888 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5888 "FStar.HyperStack.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5890; FStar_Extraction_ML_Syntax.loc = uu____5891}, (uu____5892)::[]) when (

let uu____5895 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5895 "FStar.HyperStack.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5897; FStar_Extraction_ML_Syntax.loc = uu____5898}, uu____5899); FStar_Extraction_ML_Syntax.mlty = uu____5900; FStar_Extraction_ML_Syntax.loc = uu____5901}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (((

let uu____5915 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5915 "FStar.Buffer.blit")) || (

let uu____5917 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5917 "LowStar.Monotonic.Buffer.blit"))) || (

let uu____5919 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5919 "LowStar.UninitializedBuffer.ublit"))) -> begin
(

let uu____5920 = (

let uu____5931 = (translate_expr env e1)
in (

let uu____5932 = (translate_expr env e2)
in (

let uu____5933 = (translate_expr env e3)
in (

let uu____5934 = (translate_expr env e4)
in (

let uu____5935 = (translate_expr env e5)
in ((uu____5931), (uu____5932), (uu____5933), (uu____5934), (uu____5935)))))))
in EBufBlit (uu____5920))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5937; FStar_Extraction_ML_Syntax.loc = uu____5938}, uu____5939); FStar_Extraction_ML_Syntax.mlty = uu____5940; FStar_Extraction_ML_Syntax.loc = uu____5941}, (e1)::(e2)::(e3)::[]) when (

let uu____5951 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5951 "FStar.Buffer.fill")) -> begin
(

let uu____5952 = (

let uu____5959 = (translate_expr env e1)
in (

let uu____5960 = (translate_expr env e2)
in (

let uu____5961 = (translate_expr env e3)
in ((uu____5959), (uu____5960), (uu____5961)))))
in EBufFill (uu____5952))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5963; FStar_Extraction_ML_Syntax.loc = uu____5964}, (uu____5965)::[]) when (

let uu____5968 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5968 "FStar.HyperStack.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5970; FStar_Extraction_ML_Syntax.loc = uu____5971}, uu____5972); FStar_Extraction_ML_Syntax.mlty = uu____5973; FStar_Extraction_ML_Syntax.loc = uu____5974}, (_ebuf)::(_eseq)::[]) when ((((

let uu____5985 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5985 "LowStar.Monotonic.Buffer.witness_p")) || (

let uu____5987 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5987 "LowStar.Monotonic.Buffer.recall_p"))) || (

let uu____5989 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5989 "LowStar.ImmutableBuffer.witness_contents"))) || (

let uu____5991 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5991 "LowStar.ImmutableBuffer.recall_contents"))) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5993; FStar_Extraction_ML_Syntax.loc = uu____5994}, (e1)::[]) when (

let uu____5998 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5998 "Obj.repr")) -> begin
(

let uu____5999 = (

let uu____6004 = (translate_expr env e1)
in ((uu____6004), (TAny)))
in ECast (uu____5999))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____6007; FStar_Extraction_ML_Syntax.loc = uu____6008}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____6016 = (FStar_Util.must (mk_width m))
in (

let uu____6017 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____6016 uu____6017 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____6019; FStar_Extraction_ML_Syntax.loc = uu____6020}, args) when (is_bool_op op) -> begin
(

let uu____6028 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____6028 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____6030; FStar_Extraction_ML_Syntax.loc = uu____6031}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____6033; FStar_Extraction_ML_Syntax.loc = uu____6034})::[]) when (is_machine_int m) -> begin
(

let uu____6049 = (

let uu____6054 = (FStar_Util.must (mk_width m))
in ((uu____6054), (c)))
in EConstant (uu____6049))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____6056; FStar_Extraction_ML_Syntax.loc = uu____6057}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____6059; FStar_Extraction_ML_Syntax.loc = uu____6060})::[]) when (is_machine_int m) -> begin
(

let uu____6075 = (

let uu____6080 = (FStar_Util.must (mk_width m))
in ((uu____6080), (c)))
in EConstant (uu____6075))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____6081; FStar_Extraction_ML_Syntax.loc = uu____6082}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____6084; FStar_Extraction_ML_Syntax.loc = uu____6085})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____6091 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::("String")::[], "of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____6092; FStar_Extraction_ML_Syntax.loc = uu____6093}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____6095; FStar_Extraction_ML_Syntax.loc = uu____6096})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____6102 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____6104; FStar_Extraction_ML_Syntax.loc = uu____6105}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____6112 = (

let uu____6117 = (translate_expr env arg)
in ((uu____6117), (TInt (UInt64))))
in ECast (uu____6112))
end
| uu____6118 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____6119 = (

let uu____6124 = (translate_expr env arg)
in ((uu____6124), (TInt (UInt32))))
in ECast (uu____6119))
end
| uu____6125 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____6126 = (

let uu____6131 = (translate_expr env arg)
in ((uu____6131), (TInt (UInt16))))
in ECast (uu____6126))
end
| uu____6132 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____6133 = (

let uu____6138 = (translate_expr env arg)
in ((uu____6138), (TInt (UInt8))))
in ECast (uu____6133))
end
| uu____6139 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____6140 = (

let uu____6145 = (translate_expr env arg)
in ((uu____6145), (TInt (Int64))))
in ECast (uu____6140))
end
| uu____6146 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____6147 = (

let uu____6152 = (translate_expr env arg)
in ((uu____6152), (TInt (Int32))))
in ECast (uu____6147))
end
| uu____6153 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____6154 = (

let uu____6159 = (translate_expr env arg)
in ((uu____6159), (TInt (Int16))))
in ECast (uu____6154))
end
| uu____6160 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____6161 = (

let uu____6166 = (translate_expr env arg)
in ((uu____6166), (TInt (Int8))))
in ECast (uu____6161))
end
| uu____6167 -> begin
(

let uu____6168 = (

let uu____6175 = (

let uu____6178 = (translate_expr env arg)
in (uu____6178)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____6175)))
in EApp (uu____6168))
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

let uu____6189 = (

let uu____6196 = (translate_expr env head1)
in (

let uu____6197 = (FStar_List.map (translate_expr env) args)
in ((uu____6196), (uu____6197))))
in EApp (uu____6189))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(

let uu____6208 = (

let uu____6215 = (translate_expr env head1)
in (

let uu____6216 = (FStar_List.map (translate_type env) ty_args)
in ((uu____6215), (uu____6216))))
in ETypApp (uu____6208))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) -> begin
(

let uu____6224 = (

let uu____6229 = (translate_expr env e1)
in (

let uu____6230 = (translate_type env t_to)
in ((uu____6229), (uu____6230))))
in ECast (uu____6224))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____6231, fields) -> begin
(

let uu____6249 = (

let uu____6260 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____6261 = (FStar_List.map (fun uu____6280 -> (match (uu____6280) with
| (field, expr) -> begin
(

let uu____6291 = (translate_expr env expr)
in ((field), (uu____6291)))
end)) fields)
in ((uu____6260), (uu____6261))))
in EFlat (uu____6249))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) -> begin
(

let uu____6300 = (

let uu____6307 = (assert_lid env e1.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____6308 = (translate_expr env e1)
in ((uu____6307), (uu____6308), ((FStar_Pervasives_Native.snd path)))))
in EField (uu____6300))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____6311) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, uu____6323) -> begin
(

let uu____6328 = (

let uu____6329 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head1)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____6329))
in (failwith uu____6328))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____6335 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____6335))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____6341 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____6341))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____6344, cons1), es) -> begin
(

let uu____6355 = (

let uu____6364 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____6365 = (FStar_List.map (translate_expr env) es)
in ((uu____6364), (cons1), (uu____6365))))
in ECons (uu____6355))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env1 = (add_binders env args)
in (

let uu____6388 = (

let uu____6397 = (translate_expr env1 body)
in (

let uu____6398 = (translate_type env1 body.FStar_Extraction_ML_Syntax.mlty)
in ((binders), (uu____6397), (uu____6398))))
in EFun (uu____6388))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____6408 = (

let uu____6415 = (translate_expr env e1)
in (

let uu____6416 = (translate_expr env e2)
in (

let uu____6417 = (match (e3) with
| FStar_Pervasives_Native.None -> begin
EUnit
end
| FStar_Pervasives_Native.Some (e31) -> begin
(translate_expr env e31)
end)
in ((uu____6415), (uu____6416), (uu____6417)))))
in EIfThenElse (uu____6408))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____6419) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____6426) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____6441) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6456 = (

let uu____6469 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____6469)))
in TApp (uu____6456))
end
| uu____6480 -> begin
TQualified (lid)
end)
end
| uu____6481 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____6507 -> (match (uu____6507) with
| (pat, guard, expr) -> begin
(match ((Prims.op_Equality guard FStar_Pervasives_Native.None)) with
| true -> begin
(

let uu____6533 = (translate_pat env pat)
in (match (uu____6533) with
| (env1, pat1) -> begin
(

let uu____6544 = (translate_expr env1 expr)
in ((pat1), (uu____6544)))
end))
end
| uu____6545 -> begin
(failwith "todo: translate_branch")
end)
end))
and translate_width : (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option  ->  width = (fun uu___288_6550 -> (match (uu___288_6550) with
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

let uu____6614 = (

let uu____6615 = (

let uu____6620 = (translate_width sw)
in ((uu____6620), (s)))
in PConstant (uu____6615))
in ((env), (uu____6614)))
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
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6624, cons1), ps) -> begin
(

let uu____6635 = (FStar_List.fold_left (fun uu____6655 p1 -> (match (uu____6655) with
| (env1, acc) -> begin
(

let uu____6675 = (translate_pat env1 p1)
in (match (uu____6675) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____6635) with
| (env1, ps1) -> begin
((env1), (PCons (((cons1), ((FStar_List.rev ps1))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____6704, ps) -> begin
(

let uu____6722 = (FStar_List.fold_left (fun uu____6756 uu____6757 -> (match (((uu____6756), (uu____6757))) with
| ((env1, acc), (field, p1)) -> begin
(

let uu____6826 = (translate_pat env1 p1)
in (match (uu____6826) with
| (env2, p2) -> begin
((env2), ((((field), (p2)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____6722) with
| (env1, ps1) -> begin
((env1), (PRecord ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____6888 = (FStar_List.fold_left (fun uu____6908 p1 -> (match (uu____6908) with
| (env1, acc) -> begin
(

let uu____6928 = (translate_pat env1 p1)
in (match (uu____6928) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____6888) with
| (env1, ps1) -> begin
((env1), (PTuple ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____6955) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____6960) -> begin
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

let uu____6971 = (

let uu____6972 = (FStar_String.list_of_string s)
in (FStar_All.pipe_right uu____6972 (FStar_Util.for_some (fun c1 -> (Prims.op_Equality c1 (FStar_Char.char_of_int (Prims.parse_int "0")))))))
in (match (uu____6971) with
| true -> begin
(

let uu____6984 = (FStar_Util.format1 "Refusing to translate a string literal that contains a null character: %s" s)
in (failwith uu____6984))
end
| uu____6985 -> begin
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
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____6997)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____7012) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____7013) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) -> begin
EConstant (((CInt), (s)))
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____7033 = (

let uu____7040 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____7040)))
in EApp (uu____7033)))




