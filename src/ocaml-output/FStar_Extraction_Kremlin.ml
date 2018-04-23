
open Prims
open FStar_Pervasives
type decl =
| DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int * typ * expr)
| DFunction of (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ * (Prims.string Prims.list * Prims.string) * binder Prims.list * expr)
| DTypeAlias of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * typ)
| DTypeFlat of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list)
| DExternal of (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string Prims.list * Prims.string) * typ)
| DTypeVariant of ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int * (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list) 
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
{name : Prims.string; typ : typ} 
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
| uu____616 -> begin
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
| uu____710 -> begin
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
| uu____818 -> begin
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
| uu____906 -> begin
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
| uu____1016 -> begin
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
| uu____1116 -> begin
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
| uu____1225 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____1231 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____1237 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1243 -> begin
false
end))


let uu___is_WipeBody : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WipeBody -> begin
true
end
| uu____1249 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1255 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1261 -> begin
false
end))


let uu___is_GCType : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GCType -> begin
true
end
| uu____1267 -> begin
false
end))


let uu___is_Comment : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____1274 -> begin
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
| uu____1287 -> begin
false
end))


let uu___is_Const : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____1294 -> begin
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
| uu____1308 -> begin
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
| uu____1322 -> begin
false
end))


let __proj__Epilogue__item___0 : flag  ->  Prims.string = (fun projectee -> (match (projectee) with
| Epilogue (_0) -> begin
_0
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____1335 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____1341 -> begin
false
end))


let uu___is_ManuallyManaged : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ManuallyManaged -> begin
true
end
| uu____1347 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____1354 -> begin
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
| uu____1374 -> begin
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
| uu____1410 -> begin
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
| uu____1435 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____1448 -> begin
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
| uu____1486 -> begin
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
| uu____1524 -> begin
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
| uu____1562 -> begin
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
| uu____1596 -> begin
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
| uu____1620 -> begin
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
| uu____1652 -> begin
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
| uu____1688 -> begin
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
| uu____1720 -> begin
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
| uu____1756 -> begin
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
| uu____1792 -> begin
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
| uu____1846 -> begin
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
| uu____1894 -> begin
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
| uu____1924 -> begin
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
| uu____1949 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____1955 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____1962 -> begin
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
| uu____1975 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____1981 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____1988 -> begin
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
| uu____2012 -> begin
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
| uu____2062 -> begin
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
| uu____2098 -> begin
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
| uu____2130 -> begin
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
| uu____2164 -> begin
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
| uu____2192 -> begin
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
| uu____2236 -> begin
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
| uu____2268 -> begin
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
| uu____2290 -> begin
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
| uu____2328 -> begin
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
| uu____2342 -> begin
false
end))


let __proj__EBufFree__item___0 : expr  ->  expr = (fun projectee -> (match (projectee) with
| EBufFree (_0) -> begin
_0
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____2355 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____2361 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____2367 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____2373 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____2379 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____2385 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____2391 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____2397 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____2403 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____2409 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____2415 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____2421 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____2427 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____2433 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____2439 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____2445 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____2451 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____2457 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____2463 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____2469 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____2475 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____2481 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____2487 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____2493 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____2499 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____2505 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____2512 -> begin
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
| uu____2526 -> begin
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
| uu____2546 -> begin
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
| uu____2580 -> begin
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
| uu____2606 -> begin
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
| uu____2642 -> begin
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
| uu____2667 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____2673 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____2679 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____2685 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____2691 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____2697 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____2703 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____2709 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____2715 -> begin
false
end))


let uu___is_CInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInt -> begin
true
end
| uu____2721 -> begin
false
end))


let __proj__Mkbinder__item__name : binder  ->  Prims.string = (fun projectee -> (match (projectee) with
| {name = __fname__name; typ = __fname__typ} -> begin
__fname__name
end))


let __proj__Mkbinder__item__typ : binder  ->  typ = (fun projectee -> (match (projectee) with
| {name = __fname__name; typ = __fname__typ} -> begin
__fname__typ
end))


let uu___is_TInt : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TInt (_0) -> begin
true
end
| uu____2742 -> begin
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
| uu____2756 -> begin
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
| uu____2769 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____2782 -> begin
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
| uu____2813 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____2819 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____2830 -> begin
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
| uu____2856 -> begin
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
| uu____2882 -> begin
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
| uu____2934 -> begin
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


let fst3 : 'Auu____3014 'Auu____3015 'Auu____3016 . ('Auu____3014 * 'Auu____3015 * 'Auu____3016)  ->  'Auu____3014 = (fun uu____3027 -> (match (uu____3027) with
| (x, uu____3035, uu____3036) -> begin
x
end))


let snd3 : 'Auu____3045 'Auu____3046 'Auu____3047 . ('Auu____3045 * 'Auu____3046 * 'Auu____3047)  ->  'Auu____3046 = (fun uu____3058 -> (match (uu____3058) with
| (uu____3065, x, uu____3067) -> begin
x
end))


let thd3 : 'Auu____3076 'Auu____3077 'Auu____3078 . ('Auu____3076 * 'Auu____3077 * 'Auu____3078)  ->  'Auu____3078 = (fun uu____3089 -> (match (uu____3089) with
| (uu____3096, uu____3097, x) -> begin
x
end))


let mk_width : Prims.string  ->  width FStar_Pervasives_Native.option = (fun uu___35_3105 -> (match (uu___35_3105) with
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
| uu____3108 -> begin
FStar_Pervasives_Native.None
end))


let mk_bool_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___36_3115 -> (match (uu___36_3115) with
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
| uu____3118 -> begin
FStar_Pervasives_Native.None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> (Prims.op_disEquality (mk_bool_op op) FStar_Pervasives_Native.None))


let mk_op : Prims.string  ->  op FStar_Pervasives_Native.option = (fun uu___37_3132 -> (match (uu___37_3132) with
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
| uu____3135 -> begin
FStar_Pervasives_Native.None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> (Prims.op_disEquality (mk_op op) FStar_Pervasives_Native.None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> (Prims.op_disEquality (mk_width m) FStar_Pervasives_Native.None))

type env =
{names : name Prims.list; names_t : Prims.string Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string}


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
| {pretty = __fname__pretty} -> begin
__fname__pretty
end))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; names_t = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___42_3255 = env
in {names = ({pretty = x})::env.names; names_t = uu___42_3255.names_t; module_name = uu___42_3255.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let uu___43_3266 = env
in {names = uu___43_3266.names; names_t = (x)::env.names_t; module_name = uu___43_3266.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____3277 = (FStar_List.tryFind (fun name -> (Prims.op_Equality name.pretty x)) env.names)
in (match (uu____3277) with
| FStar_Pervasives_Native.Some (name) -> begin
name
end
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: name not found")
end)))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_All.try_with (fun uu___45_3294 -> (match (()) with
| () -> begin
(FStar_List.index (fun name -> (Prims.op_Equality name.pretty x)) env.names)
end)) (fun uu___44_3300 -> (match (uu___44_3300) with
| uu____3301 -> begin
(

let uu____3302 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____3302))
end))))


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_All.try_with (fun uu___47_3314 -> (match (()) with
| () -> begin
(FStar_List.index (fun name -> (Prims.op_Equality name x)) env.names_t)
end)) (fun uu___46_3320 -> (match (uu___46_3320) with
| uu____3321 -> begin
(

let uu____3322 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith uu____3322))
end))))


let add_binders : 'Auu____3329 . env  ->  (Prims.string * 'Auu____3329) Prims.list  ->  env = (fun env binders -> (FStar_List.fold_left (fun env1 uu____3361 -> (match (uu____3361) with
| (name, uu____3367) -> begin
(extend env1 name)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____3572 -> (match (uu____3572) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____3620 = m
in (match (uu____3620) with
| (path, uu____3634, uu____3635) -> begin
(FStar_Extraction_ML_Syntax.string_of_mlpath path)
end))
in (FStar_All.try_with (fun uu___49_3653 -> (match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
(

let uu____3657 = (translate_module m)
in FStar_Pervasives_Native.Some (uu____3657));
)
end)) (fun uu___48_3661 -> (match (uu___48_3661) with
| e -> begin
((

let uu____3666 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name uu____3666));
FStar_Pervasives_Native.None;
)
end))))) modules)
end))
and translate_module : (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____3667 -> (match (uu____3667) with
| (module_name, modul, uu____3682) -> begin
(

let module_name1 = (FStar_List.append (FStar_Pervasives_Native.fst module_name) (((FStar_Pervasives_Native.snd module_name))::[]))
in (

let program = (match (modul) with
| FStar_Pervasives_Native.Some (_signature, decls) -> begin
(FStar_List.collect (translate_decl (empty module_name1)) decls)
end
| uu____3713 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name1)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.meta Prims.list  ->  flag Prims.list = (fun flags1 -> (FStar_List.choose (fun uu___38_3726 -> (match (uu___38_3726) with
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
| uu____3733 -> begin
FStar_Pervasives_Native.None
end)) flags1))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.list = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) -> begin
(FStar_List.choose (translate_let env flavor) lbs)
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____3744) -> begin
[]
end
| FStar_Extraction_ML_Syntax.MLM_Ty (tys) -> begin
(FStar_List.choose (translate_type_decl env) tys)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____3746) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____3750) -> begin
((FStar_Util.print1_warning "Skipping the translation of exception: %s\n" m);
[];
)
end))
and translate_let : env  ->  FStar_Extraction_ML_Syntax.mlletflavor  ->  FStar_Extraction_ML_Syntax.mllb  ->  decl FStar_Pervasives_Native.option = (fun env flavor lb -> (match (lb) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3772; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____3775; FStar_Extraction_ML_Syntax.loc = uu____3776}; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____3778} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3793 -> begin
(

let assumed = (FStar_Util.for_some (fun uu___39_3796 -> (match (uu___39_3796) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____3797 -> begin
false
end)) meta)
in (

let env1 = (match ((Prims.op_Equality flavor FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name)
end
| uu____3799 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 name1 -> (extend_t env2 name1)) env1 tvars)
in (

let rec find_return_type = (fun eff i uu___40_3824 -> (match (uu___40_3824) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3829, eff1, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type eff1 (i - (Prims.parse_int "1")) t)
end
| t -> begin
((eff), (t))
end))
in (

let uu____3833 = (find_return_type FStar_Extraction_ML_Syntax.E_PURE (FStar_List.length args) t0)
in (match (uu____3833) with
| (eff, t) -> begin
(

let t1 = (translate_type env2 t)
in (

let binders = (translate_binders env2 args)
in (

let env3 = (add_binders env2 args)
in (

let name1 = ((env3.module_name), (name))
in (

let meta1 = (match (((eff), (t1))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____3865) -> begin
(

let uu____3866 = (translate_flags meta)
in (MustDisappear)::uu____3866)
end
| (FStar_Extraction_ML_Syntax.E_PURE, TUnit) -> begin
(

let uu____3869 = (translate_flags meta)
in (MustDisappear)::uu____3869)
end
| uu____3872 -> begin
(translate_flags meta)
end)
in (match (assumed) with
| true -> begin
(match ((Prims.op_Equality (FStar_List.length tvars) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3881 = (

let uu____3882 = (

let uu____3901 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (meta1), (name1), (uu____3901)))
in DExternal (uu____3882))
in FStar_Pervasives_Native.Some (uu____3881))
end
| uu____3912 -> begin
((

let uu____3914 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print1_warning "No writing anything for %s (polymorphic assume)\n" uu____3914));
FStar_Pervasives_Native.None;
)
end)
end
| uu____3915 -> begin
(FStar_All.try_with (fun uu___51_3920 -> (match (()) with
| () -> begin
(

let body1 = (translate_expr env3 body)
in FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (body1)))))
end)) (fun uu___50_3941 -> (match (uu___50_3941) with
| e -> begin
(

let msg = (FStar_Util.print_exn e)
in ((

let uu____3947 = (

let uu____3952 = (

let uu____3953 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.format2 "Writing a stub for %s (%s)\n" uu____3953 msg))
in ((FStar_Errors.Warning_FunctionNotExtacted), (uu____3952)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3947));
(

let msg1 = (Prims.strcat "This function was not extracted:\n" msg)
in FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (EAbortS (msg1))))));
))
end)))
end))))))
end))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t0); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3970; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = uu____3973; FStar_Extraction_ML_Syntax.loc = uu____3974}, uu____3975, uu____3976); FStar_Extraction_ML_Syntax.mlty = uu____3977; FStar_Extraction_ML_Syntax.loc = uu____3978}; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____3980} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3995 -> begin
(

let assumed = (FStar_Util.for_some (fun uu___39_3998 -> (match (uu___39_3998) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| uu____3999 -> begin
false
end)) meta)
in (

let env1 = (match ((Prims.op_Equality flavor FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name)
end
| uu____4001 -> begin
env
end)
in (

let env2 = (FStar_List.fold_left (fun env2 name1 -> (extend_t env2 name1)) env1 tvars)
in (

let rec find_return_type = (fun eff i uu___40_4026 -> (match (uu___40_4026) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4031, eff1, t) when (i > (Prims.parse_int "0")) -> begin
(find_return_type eff1 (i - (Prims.parse_int "1")) t)
end
| t -> begin
((eff), (t))
end))
in (

let uu____4035 = (find_return_type FStar_Extraction_ML_Syntax.E_PURE (FStar_List.length args) t0)
in (match (uu____4035) with
| (eff, t) -> begin
(

let t1 = (translate_type env2 t)
in (

let binders = (translate_binders env2 args)
in (

let env3 = (add_binders env2 args)
in (

let name1 = ((env3.module_name), (name))
in (

let meta1 = (match (((eff), (t1))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____4067) -> begin
(

let uu____4068 = (translate_flags meta)
in (MustDisappear)::uu____4068)
end
| (FStar_Extraction_ML_Syntax.E_PURE, TUnit) -> begin
(

let uu____4071 = (translate_flags meta)
in (MustDisappear)::uu____4071)
end
| uu____4074 -> begin
(translate_flags meta)
end)
in (match (assumed) with
| true -> begin
(match ((Prims.op_Equality (FStar_List.length tvars) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4083 = (

let uu____4084 = (

let uu____4103 = (translate_type env3 t0)
in ((FStar_Pervasives_Native.None), (meta1), (name1), (uu____4103)))
in DExternal (uu____4084))
in FStar_Pervasives_Native.Some (uu____4083))
end
| uu____4114 -> begin
((

let uu____4116 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.print1_warning "No writing anything for %s (polymorphic assume)\n" uu____4116));
FStar_Pervasives_Native.None;
)
end)
end
| uu____4117 -> begin
(FStar_All.try_with (fun uu___51_4122 -> (match (()) with
| () -> begin
(

let body1 = (translate_expr env3 body)
in FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (body1)))))
end)) (fun uu___50_4143 -> (match (uu___50_4143) with
| e -> begin
(

let msg = (FStar_Util.print_exn e)
in ((

let uu____4149 = (

let uu____4154 = (

let uu____4155 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (FStar_Util.format2 "Writing a stub for %s (%s)\n" uu____4155 msg))
in ((FStar_Errors.Warning_FunctionNotExtacted), (uu____4154)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4149));
(

let msg1 = (Prims.strcat "This function was not extracted:\n" msg)
in FStar_Pervasives_Native.Some (DFunction (((FStar_Pervasives_Native.None), (meta1), ((FStar_List.length tvars)), (t1), (name1), (binders), (EAbortS (msg1))))));
))
end)))
end))))))
end))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (tvars, t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4172; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu____4175} -> begin
(match ((FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta)) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4178 -> begin
(

let meta1 = (translate_flags meta)
in (

let env1 = (FStar_List.fold_left (fun env1 name1 -> (extend_t env1 name1)) env tvars)
in (

let t1 = (translate_type env1 t)
in (

let name1 = ((env1.module_name), (name))
in (FStar_All.try_with (fun uu___53_4201 -> (match (()) with
| () -> begin
(

let expr1 = (translate_expr env1 expr)
in FStar_Pervasives_Native.Some (DGlobal (((meta1), (name1), ((FStar_List.length tvars)), (t1), (expr1)))))
end)) (fun uu___52_4216 -> (match (uu___52_4216) with
| e -> begin
((

let uu____4221 = (

let uu____4226 = (

let uu____4227 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in (

let uu____4228 = (FStar_Util.print_exn e)
in (FStar_Util.format2 "Not translating definition for %s (%s)\n" uu____4227 uu____4228)))
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____4226)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4221));
FStar_Pervasives_Native.Some (DGlobal (((meta1), (name1), ((FStar_List.length tvars)), (t1), (EAny))));
)
end)))))))
end)
end
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4239; FStar_Extraction_ML_Syntax.mllb_def = uu____4240; FStar_Extraction_ML_Syntax.mllb_meta = uu____4241; FStar_Extraction_ML_Syntax.print_typ = uu____4242} -> begin
((

let uu____4246 = (

let uu____4251 = (FStar_Util.format1 "Not translating definition for %s\n" name)
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____4251)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4246));
(match (ts) with
| FStar_Pervasives_Native.Some (idents, t) -> begin
(

let uu____4255 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" (FStar_String.concat ", " idents) uu____4255))
end
| FStar_Pervasives_Native.None -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
and translate_type_decl : env  ->  FStar_Extraction_ML_Syntax.one_mltydecl  ->  decl FStar_Pervasives_Native.option = (fun env ty -> (match (ty) with
| (assumed, name, _mangled_name, args, flags1, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 name2 -> (extend_t env1 name2)) env args)
in (match (assumed) with
| true -> begin
(

let name2 = (FStar_Extraction_ML_Syntax.string_of_mlpath name1)
in ((FStar_Util.print1_warning "Not translating type definition (assumed) for %s\n" name2);
FStar_Pervasives_Native.None;
))
end
| uu____4292 -> begin
(

let uu____4293 = (

let uu____4294 = (

let uu____4311 = (translate_flags flags1)
in (

let uu____4314 = (translate_type env1 t)
in ((name1), (uu____4311), ((FStar_List.length args)), (uu____4314))))
in DTypeAlias (uu____4294))
in FStar_Pervasives_Native.Some (uu____4293))
end)))
end
| (uu____4323, name, _mangled_name, args, flags1, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let env1 = (FStar_List.fold_left (fun env1 name2 -> (extend_t env1 name2)) env args)
in (

let uu____4355 = (

let uu____4356 = (

let uu____4383 = (translate_flags flags1)
in (

let uu____4386 = (FStar_List.map (fun uu____4413 -> (match (uu____4413) with
| (f, t) -> begin
(

let uu____4428 = (

let uu____4433 = (translate_type env1 t)
in ((uu____4433), (false)))
in ((f), (uu____4428)))
end)) fields)
in ((name1), (uu____4383), ((FStar_List.length args)), (uu____4386))))
in DTypeFlat (uu____4356))
in FStar_Pervasives_Native.Some (uu____4355))))
end
| (uu____4456, name, _mangled_name, args, flags1, FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))) -> begin
(

let name1 = ((env.module_name), (name))
in (

let flags2 = (translate_flags flags1)
in (

let env1 = (FStar_List.fold_left extend_t env args)
in (

let uu____4493 = (

let uu____4494 = (

let uu____4527 = (FStar_List.map (fun uu____4572 -> (match (uu____4572) with
| (cons1, ts) -> begin
(

let uu____4611 = (FStar_List.map (fun uu____4638 -> (match (uu____4638) with
| (name2, t) -> begin
(

let uu____4653 = (

let uu____4658 = (translate_type env1 t)
in ((uu____4658), (false)))
in ((name2), (uu____4653)))
end)) ts)
in ((cons1), (uu____4611)))
end)) branches)
in ((name1), (flags2), ((FStar_List.length args)), (uu____4527)))
in DTypeVariant (uu____4494))
in FStar_Pervasives_Native.Some (uu____4493)))))
end
| (uu____4697, name, _mangled_name, uu____4700, uu____4701, uu____4702) -> begin
((

let uu____4712 = (

let uu____4717 = (FStar_Util.format1 "Not translating type definition for %s\n" name)
in ((FStar_Errors.Warning_DefinitionNotTranslated), (uu____4717)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4712));
FStar_Pervasives_Native.None;
)
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Tuple ([]) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name) -> begin
(

let uu____4721 = (find_t env name)
in TBound (uu____4721))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____4723, t2) -> begin
(

let uu____4725 = (

let uu____4730 = (translate_type env t1)
in (

let uu____4731 = (translate_type env t2)
in ((uu____4730), (uu____4731))))
in TArrow (uu____4725))
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____4735 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4735 "Prims.unit")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (

let uu____4739 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4739 "Prims.bool")) -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(

let uu____4745 = (FStar_Util.must (mk_width m))
in TInt (uu____4745))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(

let uu____4751 = (FStar_Util.must (mk_width m))
in TInt (uu____4751))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (

let uu____4756 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4756 "FStar.Monotonic.HyperStack.mem")) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____4757)::(arg)::(uu____4759)::[], p) when ((((

let uu____4765 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4765 "FStar.Monotonic.HyperStack.s_mref")) || (

let uu____4767 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4767 "FStar.Monotonic.HyperHeap.mrref"))) || (

let uu____4769 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4769 "FStar.HyperStack.ST.m_rref"))) || (

let uu____4771 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4771 "FStar.HyperStack.ST.s_mref"))) -> begin
(

let uu____4772 = (translate_type env arg)
in TBuf (uu____4772))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::(uu____4774)::[], p) when (((((((((((

let uu____4780 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4780 "FStar.Monotonic.HyperStack.mreference")) || (

let uu____4782 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4782 "FStar.Monotonic.HyperStack.mstackref"))) || (

let uu____4784 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4784 "FStar.Monotonic.HyperStack.mref"))) || (

let uu____4786 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4786 "FStar.Monotonic.HyperStack.mmmstackref"))) || (

let uu____4788 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4788 "FStar.Monotonic.HyperStack.mmmref"))) || (

let uu____4790 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4790 "FStar.Monotonic.Heap.mref"))) || (

let uu____4792 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4792 "FStar.HyperStack.ST.mreference"))) || (

let uu____4794 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4794 "FStar.HyperStack.ST.mstackref"))) || (

let uu____4796 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4796 "FStar.HyperStack.ST.mref"))) || (

let uu____4798 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4798 "FStar.HyperStack.ST.mmmstackref"))) || (

let uu____4800 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4800 "FStar.HyperStack.ST.mmmref"))) -> begin
(

let uu____4801 = (translate_type env arg)
in TBuf (uu____4801))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when (((((((((((

let uu____4808 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4808 "FStar.Buffer.buffer")) || (

let uu____4810 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4810 "FStar.HyperStack.reference"))) || (

let uu____4812 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4812 "FStar.HyperStack.stackref"))) || (

let uu____4814 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4814 "FStar.HyperStack.ref"))) || (

let uu____4816 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4816 "FStar.HyperStack.mmstackref"))) || (

let uu____4818 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4818 "FStar.HyperStack.mmref"))) || (

let uu____4820 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4820 "FStar.HyperStack.ST.reference"))) || (

let uu____4822 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4822 "FStar.HyperStack.ST.stackref"))) || (

let uu____4824 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4824 "FStar.HyperStack.ST.ref"))) || (

let uu____4826 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4826 "FStar.HyperStack.ST.mmstackref"))) || (

let uu____4828 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4828 "FStar.HyperStack.ST.mmref"))) -> begin
(

let uu____4829 = (translate_type env arg)
in TBuf (uu____4829))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____4830)::(arg)::[], p) when ((

let uu____4837 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4837 "FStar.HyperStack.s_ref")) || (

let uu____4839 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4839 "FStar.HyperStack.ST.s_ref"))) -> begin
(

let uu____4840 = (translate_type env arg)
in TBuf (uu____4840))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____4841)::[], p) when (

let uu____4845 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____4845 "FStar.Ghost.erased")) -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when (((Prims.op_Equality ns (("Prims")::[])) || (Prims.op_Equality ns (("FStar")::("Pervasives")::("Native")::[]))) && (FStar_Util.starts_with t1 "tuple")) -> begin
(

let uu____4871 = (FStar_List.map (translate_type env) args)
in TTuple (uu____4871))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4880 = (

let uu____4893 = (FStar_List.map (translate_type env) args)
in ((lid), (uu____4893)))
in TApp (uu____4880))
end
| uu____4904 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____4908 = (FStar_List.map (translate_type env) ts)
in TTuple (uu____4908))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____4924 -> (match (uu____4924) with
| (name, typ) -> begin
(

let uu____4931 = (translate_type env typ)
in {name = name; typ = uu____4931})
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

let uu____4936 = (find env name)
in EBound (uu____4936))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____4941 = (

let uu____4946 = (FStar_Util.must (mk_op op))
in (

let uu____4947 = (FStar_Util.must (mk_width m))
in ((uu____4946), (uu____4947))))
in EOp (uu____4941))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(

let uu____4951 = (

let uu____4956 = (FStar_Util.must (mk_bool_op op))
in ((uu____4956), (Bool)))
in EOp (uu____4951))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n1) -> begin
EQualified (n1)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.mllb_meta = flags1; FStar_Extraction_ML_Syntax.print_typ = print7})::[]), continuation) -> begin
(

let binder = (

let uu____4975 = (translate_type env typ)
in {name = name; typ = uu____4975})
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

let uu____5001 = (

let uu____5012 = (translate_expr env expr)
in (

let uu____5013 = (translate_branches env branches)
in ((uu____5012), (uu____5013))))
in EMatch (uu____5001))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5027; FStar_Extraction_ML_Syntax.loc = uu____5028}, (t)::[]); FStar_Extraction_ML_Syntax.mlty = uu____5030; FStar_Extraction_ML_Syntax.loc = uu____5031}, (arg)::[]) when (

let uu____5037 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5037 "FStar.Dyn.undyn")) -> begin
(

let uu____5038 = (

let uu____5043 = (translate_expr env arg)
in (

let uu____5044 = (translate_type env t)
in ((uu____5043), (uu____5044))))
in ECast (uu____5038))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5046; FStar_Extraction_ML_Syntax.loc = uu____5047}, uu____5048); FStar_Extraction_ML_Syntax.mlty = uu____5049; FStar_Extraction_ML_Syntax.loc = uu____5050}, uu____5051) when (

let uu____5060 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5060 "Prims.admit")) -> begin
EAbort
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5062; FStar_Extraction_ML_Syntax.loc = uu____5063}, uu____5064); FStar_Extraction_ML_Syntax.mlty = uu____5065; FStar_Extraction_ML_Syntax.loc = uu____5066}, (arg)::[]) when (((

let uu____5076 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5076 "FStar.HyperStack.All.failwith")) || (

let uu____5078 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5078 "FStar.Error.unexpected"))) || (

let uu____5080 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5080 "FStar.Error.unreachable"))) -> begin
(match (arg) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (msg)); FStar_Extraction_ML_Syntax.mlty = uu____5082; FStar_Extraction_ML_Syntax.loc = uu____5083} -> begin
EAbortS (msg)
end
| uu____5084 -> begin
(

let print7 = (

let uu____5086 = (

let uu____5087 = (

let uu____5088 = (FStar_Ident.lid_of_str "FStar.HyperStack.IO.print_string")
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5088))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____5087))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____5086))
in (

let print8 = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top (FStar_Extraction_ML_Syntax.MLE_App (((print7), ((arg)::[])))))
in (

let t = (translate_expr env print8)
in ESequence ((t)::(EAbort)::[]))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5094; FStar_Extraction_ML_Syntax.loc = uu____5095}, uu____5096); FStar_Extraction_ML_Syntax.mlty = uu____5097; FStar_Extraction_ML_Syntax.loc = uu____5098}, (e1)::(e2)::[]) when ((

let uu____5109 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5109 "FStar.Buffer.index")) || (

let uu____5111 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5111 "FStar.Buffer.op_Array_Access"))) -> begin
(

let uu____5112 = (

let uu____5117 = (translate_expr env e1)
in (

let uu____5118 = (translate_expr env e2)
in ((uu____5117), (uu____5118))))
in EBufRead (uu____5112))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5120; FStar_Extraction_ML_Syntax.loc = uu____5121}, uu____5122); FStar_Extraction_ML_Syntax.mlty = uu____5123; FStar_Extraction_ML_Syntax.loc = uu____5124}, (e1)::[]) when (

let uu____5132 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5132 "FStar.HyperStack.ST.op_Bang")) -> begin
(

let uu____5133 = (

let uu____5138 = (translate_expr env e1)
in ((uu____5138), (EConstant (((UInt32), ("0"))))))
in EBufRead (uu____5133))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5140; FStar_Extraction_ML_Syntax.loc = uu____5141}, uu____5142); FStar_Extraction_ML_Syntax.mlty = uu____5143; FStar_Extraction_ML_Syntax.loc = uu____5144}, (e1)::(e2)::[]) when (

let uu____5153 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5153 "FStar.Buffer.create")) -> begin
(

let uu____5154 = (

let uu____5161 = (translate_expr env e1)
in (

let uu____5162 = (translate_expr env e2)
in ((Stack), (uu____5161), (uu____5162))))
in EBufCreate (uu____5154))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5164; FStar_Extraction_ML_Syntax.loc = uu____5165}, uu____5166); FStar_Extraction_ML_Syntax.mlty = uu____5167; FStar_Extraction_ML_Syntax.loc = uu____5168}, (init1)::[]) when (

let uu____5176 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5176 "FStar.HyperStack.ST.salloc")) -> begin
(

let uu____5177 = (

let uu____5184 = (translate_expr env init1)
in ((Stack), (uu____5184), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____5177))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5186; FStar_Extraction_ML_Syntax.loc = uu____5187}, uu____5188); FStar_Extraction_ML_Syntax.mlty = uu____5189; FStar_Extraction_ML_Syntax.loc = uu____5190}, (e2)::[]) when (

let uu____5198 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5198 "FStar.Buffer.createL")) -> begin
(

let rec list_elements = (fun acc e21 -> (match (e21.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd1)::(tl1)::[]) -> begin
(list_elements ((hd1)::acc) tl1)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| uu____5228 -> begin
(failwith "Argument of FStar.Buffer.createL is not a list literal!")
end))
in (

let list_elements1 = (list_elements [])
in (

let uu____5238 = (

let uu____5245 = (

let uu____5248 = (list_elements1 e2)
in (FStar_List.map (translate_expr env) uu____5248))
in ((Stack), (uu____5245)))
in EBufCreateL (uu____5238))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5254; FStar_Extraction_ML_Syntax.loc = uu____5255}, uu____5256); FStar_Extraction_ML_Syntax.mlty = uu____5257; FStar_Extraction_ML_Syntax.loc = uu____5258}, (_rid)::(init1)::[]) when (

let uu____5267 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5267 "FStar.HyperStack.ST.ralloc")) -> begin
(

let uu____5268 = (

let uu____5275 = (translate_expr env init1)
in ((Eternal), (uu____5275), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____5268))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5277; FStar_Extraction_ML_Syntax.loc = uu____5278}, uu____5279); FStar_Extraction_ML_Syntax.mlty = uu____5280; FStar_Extraction_ML_Syntax.loc = uu____5281}, (_e0)::(e1)::(e2)::[]) when (

let uu____5291 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5291 "FStar.Buffer.rcreate")) -> begin
(

let uu____5292 = (

let uu____5299 = (translate_expr env e1)
in (

let uu____5300 = (translate_expr env e2)
in ((Eternal), (uu____5299), (uu____5300))))
in EBufCreate (uu____5292))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5302; FStar_Extraction_ML_Syntax.loc = uu____5303}, uu____5304); FStar_Extraction_ML_Syntax.mlty = uu____5305; FStar_Extraction_ML_Syntax.loc = uu____5306}, (_rid)::(init1)::[]) when (

let uu____5315 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5315 "FStar.HyperStack.ST.ralloc_mm")) -> begin
(

let uu____5316 = (

let uu____5323 = (translate_expr env init1)
in ((ManuallyManaged), (uu____5323), (EConstant (((UInt32), ("1"))))))
in EBufCreate (uu____5316))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5325; FStar_Extraction_ML_Syntax.loc = uu____5326}, uu____5327); FStar_Extraction_ML_Syntax.mlty = uu____5328; FStar_Extraction_ML_Syntax.loc = uu____5329}, (_e0)::(e1)::(e2)::[]) when (

let uu____5339 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5339 "FStar.Buffer.rcreate_mm")) -> begin
(

let uu____5340 = (

let uu____5347 = (translate_expr env e1)
in (

let uu____5348 = (translate_expr env e2)
in ((ManuallyManaged), (uu____5347), (uu____5348))))
in EBufCreate (uu____5340))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5350; FStar_Extraction_ML_Syntax.loc = uu____5351}, uu____5352); FStar_Extraction_ML_Syntax.mlty = uu____5353; FStar_Extraction_ML_Syntax.loc = uu____5354}, (e2)::[]) when (

let uu____5362 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5362 "FStar.HyperStack.ST.rfree")) -> begin
(

let uu____5363 = (translate_expr env e2)
in EBufFree (uu____5363))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5365; FStar_Extraction_ML_Syntax.loc = uu____5366}, uu____5367); FStar_Extraction_ML_Syntax.mlty = uu____5368; FStar_Extraction_ML_Syntax.loc = uu____5369}, (e2)::[]) when (

let uu____5377 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5377 "FStar.Buffer.rfree")) -> begin
(

let uu____5378 = (translate_expr env e2)
in EBufFree (uu____5378))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5380; FStar_Extraction_ML_Syntax.loc = uu____5381}, uu____5382); FStar_Extraction_ML_Syntax.mlty = uu____5383; FStar_Extraction_ML_Syntax.loc = uu____5384}, (e1)::(e2)::(_e3)::[]) when (

let uu____5394 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5394 "FStar.Buffer.sub")) -> begin
(

let uu____5395 = (

let uu____5400 = (translate_expr env e1)
in (

let uu____5401 = (translate_expr env e2)
in ((uu____5400), (uu____5401))))
in EBufSub (uu____5395))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5403; FStar_Extraction_ML_Syntax.loc = uu____5404}, uu____5405); FStar_Extraction_ML_Syntax.mlty = uu____5406; FStar_Extraction_ML_Syntax.loc = uu____5407}, (e1)::(e2)::[]) when (

let uu____5416 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5416 "FStar.Buffer.join")) -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5418; FStar_Extraction_ML_Syntax.loc = uu____5419}, uu____5420); FStar_Extraction_ML_Syntax.mlty = uu____5421; FStar_Extraction_ML_Syntax.loc = uu____5422}, (e1)::(e2)::[]) when (

let uu____5431 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5431 "FStar.Buffer.offset")) -> begin
(

let uu____5432 = (

let uu____5437 = (translate_expr env e1)
in (

let uu____5438 = (translate_expr env e2)
in ((uu____5437), (uu____5438))))
in EBufSub (uu____5432))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5440; FStar_Extraction_ML_Syntax.loc = uu____5441}, uu____5442); FStar_Extraction_ML_Syntax.mlty = uu____5443; FStar_Extraction_ML_Syntax.loc = uu____5444}, (e1)::(e2)::(e3)::[]) when ((

let uu____5456 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5456 "FStar.Buffer.upd")) || (

let uu____5458 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5458 "FStar.Buffer.op_Array_Assignment"))) -> begin
(

let uu____5459 = (

let uu____5466 = (translate_expr env e1)
in (

let uu____5467 = (translate_expr env e2)
in (

let uu____5468 = (translate_expr env e3)
in ((uu____5466), (uu____5467), (uu____5468)))))
in EBufWrite (uu____5459))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5470; FStar_Extraction_ML_Syntax.loc = uu____5471}, uu____5472); FStar_Extraction_ML_Syntax.mlty = uu____5473; FStar_Extraction_ML_Syntax.loc = uu____5474}, (e1)::(e2)::[]) when (

let uu____5483 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5483 "FStar.HyperStack.ST.op_Colon_Equals")) -> begin
(

let uu____5484 = (

let uu____5491 = (translate_expr env e1)
in (

let uu____5492 = (translate_expr env e2)
in ((uu____5491), (EConstant (((UInt32), ("0")))), (uu____5492))))
in EBufWrite (uu____5484))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5494; FStar_Extraction_ML_Syntax.loc = uu____5495}, (uu____5496)::[]) when (

let uu____5499 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5499 "FStar.HyperStack.ST.push_frame")) -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5501; FStar_Extraction_ML_Syntax.loc = uu____5502}, (uu____5503)::[]) when (

let uu____5506 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5506 "FStar.HyperStack.ST.pop_frame")) -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5508; FStar_Extraction_ML_Syntax.loc = uu____5509}, uu____5510); FStar_Extraction_ML_Syntax.mlty = uu____5511; FStar_Extraction_ML_Syntax.loc = uu____5512}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when (

let uu____5524 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5524 "FStar.Buffer.blit")) -> begin
(

let uu____5525 = (

let uu____5536 = (translate_expr env e1)
in (

let uu____5537 = (translate_expr env e2)
in (

let uu____5538 = (translate_expr env e3)
in (

let uu____5539 = (translate_expr env e4)
in (

let uu____5540 = (translate_expr env e5)
in ((uu____5536), (uu____5537), (uu____5538), (uu____5539), (uu____5540)))))))
in EBufBlit (uu____5525))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5542; FStar_Extraction_ML_Syntax.loc = uu____5543}, uu____5544); FStar_Extraction_ML_Syntax.mlty = uu____5545; FStar_Extraction_ML_Syntax.loc = uu____5546}, (e1)::(e2)::(e3)::[]) when (

let uu____5556 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5556 "FStar.Buffer.fill")) -> begin
(

let uu____5557 = (

let uu____5564 = (translate_expr env e1)
in (

let uu____5565 = (translate_expr env e2)
in (

let uu____5566 = (translate_expr env e3)
in ((uu____5564), (uu____5565), (uu____5566)))))
in EBufFill (uu____5557))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5568; FStar_Extraction_ML_Syntax.loc = uu____5569}, (uu____5570)::[]) when (

let uu____5573 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5573 "FStar.HyperStack.ST.get")) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____5575; FStar_Extraction_ML_Syntax.loc = uu____5576}, (e1)::[]) when (

let uu____5580 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____5580 "Obj.repr")) -> begin
(

let uu____5581 = (

let uu____5586 = (translate_expr env e1)
in ((uu____5586), (TAny)))
in ECast (uu____5581))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____5589; FStar_Extraction_ML_Syntax.loc = uu____5590}, args) when ((is_machine_int m) && (is_op op)) -> begin
(

let uu____5598 = (FStar_Util.must (mk_width m))
in (

let uu____5599 = (FStar_Util.must (mk_op op))
in (mk_op_app env uu____5598 uu____5599 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____5601; FStar_Extraction_ML_Syntax.loc = uu____5602}, args) when (is_bool_op op) -> begin
(

let uu____5610 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool uu____5610 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____5612; FStar_Extraction_ML_Syntax.loc = uu____5613}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____5615; FStar_Extraction_ML_Syntax.loc = uu____5616})::[]) when (is_machine_int m) -> begin
(

let uu____5631 = (

let uu____5636 = (FStar_Util.must (mk_width m))
in ((uu____5636), (c)))
in EConstant (uu____5631))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = uu____5638; FStar_Extraction_ML_Syntax.loc = uu____5639}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, FStar_Pervasives_Native.None)); FStar_Extraction_ML_Syntax.mlty = uu____5641; FStar_Extraction_ML_Syntax.loc = uu____5642})::[]) when (is_machine_int m) -> begin
(

let uu____5657 = (

let uu____5662 = (FStar_Util.must (mk_width m))
in ((uu____5662), (c)))
in EConstant (uu____5657))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____5663; FStar_Extraction_ML_Syntax.loc = uu____5664}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____5666; FStar_Extraction_ML_Syntax.loc = uu____5667})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____5673 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::("String")::[], "of_literal"); FStar_Extraction_ML_Syntax.mlty = uu____5674; FStar_Extraction_ML_Syntax.loc = uu____5675}, ({FStar_Extraction_ML_Syntax.expr = e1; FStar_Extraction_ML_Syntax.mlty = uu____5677; FStar_Extraction_ML_Syntax.loc = uu____5678})::[]) -> begin
(match (e1) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| uu____5684 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____5686; FStar_Extraction_ML_Syntax.loc = uu____5687}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
(

let uu____5694 = (

let uu____5699 = (translate_expr env arg)
in ((uu____5699), (TInt (UInt64))))
in ECast (uu____5694))
end
| uu____5700 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
(

let uu____5701 = (

let uu____5706 = (translate_expr env arg)
in ((uu____5706), (TInt (UInt32))))
in ECast (uu____5701))
end
| uu____5707 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
(

let uu____5708 = (

let uu____5713 = (translate_expr env arg)
in ((uu____5713), (TInt (UInt16))))
in ECast (uu____5708))
end
| uu____5714 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
(

let uu____5715 = (

let uu____5720 = (translate_expr env arg)
in ((uu____5720), (TInt (UInt8))))
in ECast (uu____5715))
end
| uu____5721 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
(

let uu____5722 = (

let uu____5727 = (translate_expr env arg)
in ((uu____5727), (TInt (Int64))))
in ECast (uu____5722))
end
| uu____5728 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
(

let uu____5729 = (

let uu____5734 = (translate_expr env arg)
in ((uu____5734), (TInt (Int32))))
in ECast (uu____5729))
end
| uu____5735 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
(

let uu____5736 = (

let uu____5741 = (translate_expr env arg)
in ((uu____5741), (TInt (Int16))))
in ECast (uu____5736))
end
| uu____5742 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
(

let uu____5743 = (

let uu____5748 = (translate_expr env arg)
in ((uu____5748), (TInt (Int8))))
in ECast (uu____5743))
end
| uu____5749 -> begin
(

let uu____5750 = (

let uu____5757 = (

let uu____5760 = (translate_expr env arg)
in (uu____5760)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (uu____5757)))
in EApp (uu____5750))
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

let uu____5771 = (

let uu____5778 = (translate_expr env head1)
in (

let uu____5779 = (FStar_List.map (translate_expr env) args)
in ((uu____5778), (uu____5779))))
in EApp (uu____5771))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(

let uu____5790 = (

let uu____5797 = (translate_expr env head1)
in (

let uu____5798 = (FStar_List.map (translate_type env) ty_args)
in ((uu____5797), (uu____5798))))
in ETypApp (uu____5790))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) -> begin
(

let uu____5806 = (

let uu____5811 = (translate_expr env e1)
in (

let uu____5812 = (translate_type env t_to)
in ((uu____5811), (uu____5812))))
in ECast (uu____5806))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____5813, fields) -> begin
(

let uu____5831 = (

let uu____5842 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5843 = (FStar_List.map (fun uu____5862 -> (match (uu____5862) with
| (field, expr) -> begin
(

let uu____5873 = (translate_expr env expr)
in ((field), (uu____5873)))
end)) fields)
in ((uu____5842), (uu____5843))))
in EFlat (uu____5831))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) -> begin
(

let uu____5882 = (

let uu____5889 = (assert_lid env e1.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5890 = (translate_expr env e1)
in ((uu____5889), (uu____5890), ((FStar_Pervasives_Native.snd path)))))
in EField (uu____5882))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____5893) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head1, uu____5905) -> begin
(

let uu____5910 = (

let uu____5911 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head1)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" uu____5911))
in (failwith uu____5910))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(

let uu____5917 = (FStar_List.map (translate_expr env) seqs)
in ESequence (uu____5917))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let uu____5923 = (FStar_List.map (translate_expr env) es)
in ETuple (uu____5923))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5926, cons1), es) -> begin
(

let uu____5937 = (

let uu____5946 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (

let uu____5947 = (FStar_List.map (translate_expr env) es)
in ((uu____5946), (cons1), (uu____5947))))
in ECons (uu____5937))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let binders = (translate_binders env args)
in (

let env1 = (add_binders env args)
in (

let uu____5970 = (

let uu____5979 = (translate_expr env1 body)
in (

let uu____5980 = (translate_type env1 body.FStar_Extraction_ML_Syntax.mlty)
in ((binders), (uu____5979), (uu____5980))))
in EFun (uu____5970))))
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(

let uu____5990 = (

let uu____5997 = (translate_expr env e1)
in (

let uu____5998 = (translate_expr env e2)
in (

let uu____5999 = (match (e3) with
| FStar_Pervasives_Native.None -> begin
EUnit
end
| FStar_Pervasives_Native.Some (e31) -> begin
(translate_expr env e31)
end)
in ((uu____5997), (uu____5998), (uu____5999)))))
in EIfThenElse (uu____5990))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____6001) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____6008) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____6023) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6038 = (

let uu____6051 = (FStar_List.map (translate_type env) ts)
in ((lid), (uu____6051)))
in TApp (uu____6038))
end
| uu____6062 -> begin
TQualified (lid)
end)
end
| uu____6063 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____6089 -> (match (uu____6089) with
| (pat, guard, expr) -> begin
(match ((Prims.op_Equality guard FStar_Pervasives_Native.None)) with
| true -> begin
(

let uu____6115 = (translate_pat env pat)
in (match (uu____6115) with
| (env1, pat1) -> begin
(

let uu____6126 = (translate_expr env1 expr)
in ((pat1), (uu____6126)))
end))
end
| uu____6127 -> begin
(failwith "todo: translate_branch")
end)
end))
and translate_width : (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option  ->  width = (fun uu___41_6132 -> (match (uu___41_6132) with
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

let uu____6196 = (

let uu____6197 = (

let uu____6202 = (translate_width sw)
in ((uu____6202), (s)))
in PConstant (uu____6197))
in ((env), (uu____6196)))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name) -> begin
(

let env1 = (extend env name)
in ((env1), (PVar ({name = name; typ = TAny}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env1 = (extend env "_")
in ((env1), (PVar ({name = "_"; typ = TAny}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6206, cons1), ps) -> begin
(

let uu____6217 = (FStar_List.fold_left (fun uu____6237 p1 -> (match (uu____6237) with
| (env1, acc) -> begin
(

let uu____6257 = (translate_pat env1 p1)
in (match (uu____6257) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____6217) with
| (env1, ps1) -> begin
((env1), (PCons (((cons1), ((FStar_List.rev ps1))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (uu____6286, ps) -> begin
(

let uu____6304 = (FStar_List.fold_left (fun uu____6338 uu____6339 -> (match (((uu____6338), (uu____6339))) with
| ((env1, acc), (field, p1)) -> begin
(

let uu____6408 = (translate_pat env1 p1)
in (match (uu____6408) with
| (env2, p2) -> begin
((env2), ((((field), (p2)))::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____6304) with
| (env1, ps1) -> begin
((env1), (PRecord ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let uu____6470 = (FStar_List.fold_left (fun uu____6490 p1 -> (match (uu____6490) with
| (env1, acc) -> begin
(

let uu____6510 = (translate_pat env1 p1)
in (match (uu____6510) with
| (env2, p2) -> begin
((env2), ((p2)::acc))
end))
end)) ((env), ([])) ps)
in (match (uu____6470) with
| (env1, ps1) -> begin
((env1), (PTuple ((FStar_List.rev ps1))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (uu____6537) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____6542) -> begin
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

let uu____6553 = (

let uu____6554 = (FStar_String.list_of_string s)
in (FStar_All.pipe_right uu____6554 (FStar_Util.for_some (fun c1 -> (Prims.op_Equality c1 (FStar_Char.char_of_int (Prims.parse_int "0")))))))
in (match (uu____6553) with
| true -> begin
(

let uu____6566 = (FStar_Util.format1 "Refusing to translate a string literal that contains a null character: %s" s)
in (failwith uu____6566))
end
| uu____6567 -> begin
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
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____6578)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____6593) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____6594) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) -> begin
EConstant (((CInt), (s)))
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (

let uu____6614 = (

let uu____6621 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (uu____6621)))
in EApp (uu____6614)))




