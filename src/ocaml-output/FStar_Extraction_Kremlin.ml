
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
<<<<<<< HEAD
| ECons of (typ * Prims.string * expr Prims.list)
| EBufFill of (expr * expr * expr) 
=======
| ECons of (typ * ident * expr Prims.list)
| EBufFill of (expr * expr * expr)
| EString of Prims.string 
>>>>>>> origin/master
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
| uu____290 -> begin
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
| uu____338 -> begin
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
| uu____392 -> begin
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
| uu____433 -> begin
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
| uu____485 -> begin
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
| uu____532 -> begin
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
| uu____585 -> begin
false
end))


let uu___is_CDecl : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CDecl -> begin
true
end
| uu____589 -> begin
false
end))


let uu___is_FastCall : cc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FastCall -> begin
true
end
| uu____593 -> begin
false
end))


let uu___is_Private : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____597 -> begin
false
end))


let uu___is_NoExtract : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____601 -> begin
false
end))


let uu___is_CInline : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____605 -> begin
false
end))


let uu___is_Substitute : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____609 -> begin
false
end))


let uu___is_Eternal : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eternal -> begin
true
end
| uu____613 -> begin
false
end))


let uu___is_Stack : lifetime  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stack -> begin
true
end
| uu____617 -> begin
false
end))


let uu___is_EBound : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBound (_0) -> begin
true
end
| uu____622 -> begin
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
| uu____637 -> begin
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
| uu____660 -> begin
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
| uu____677 -> begin
false
end))


let uu___is_EApp : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EApp (_0) -> begin
true
end
| uu____685 -> begin
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
| uu____709 -> begin
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
| uu____733 -> begin
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
| uu____755 -> begin
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
| uu____772 -> begin
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
| uu____793 -> begin
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
| uu____816 -> begin
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
| uu____837 -> begin
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
| uu____860 -> begin
false
end))


<<<<<<< HEAD
let __proj__EBufSub__item___0 : expr  ->  (expr * expr) = (fun projectee -> (match (projectee) with
| EBufSub (_0) -> begin
_0
=======
let is_EString = (fun _discr_ -> (match (_discr_) with
| EString (_) -> begin
true
end
| _ -> begin
false
end))


let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
>>>>>>> origin/master
end))


let uu___is_EBufBlit : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBufBlit (_0) -> begin
true
end
| uu____883 -> begin
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
| uu____915 -> begin
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
| uu____944 -> begin
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
| uu____964 -> begin
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
| uu____981 -> begin
false
end))


let uu___is_EPopFrame : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EPopFrame -> begin
true
end
| uu____985 -> begin
false
end))


let uu___is_EBool : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EBool (_0) -> begin
true
end
| uu____990 -> begin
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
| uu____1001 -> begin
false
end))


let uu___is_EAbort : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EAbort -> begin
true
end
| uu____1005 -> begin
false
end))


let uu___is_EReturn : expr  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EReturn (_0) -> begin
true
end
| uu____1010 -> begin
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
| uu____1027 -> begin
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
| uu____1057 -> begin
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
| uu____1080 -> begin
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
| uu____1101 -> begin
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
| uu____1123 -> begin
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
| uu____1142 -> begin
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
| uu____1169 -> begin
false
end))


let __proj__EBufFill__item___0 : expr  ->  (expr * expr * expr) = (fun projectee -> (match (projectee) with
| EBufFill (_0) -> begin
_0
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____1189 -> begin
false
end))


let uu___is_AddW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AddW -> begin
true
end
| uu____1193 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____1197 -> begin
false
end))


let uu___is_SubW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubW -> begin
true
end
| uu____1201 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____1205 -> begin
false
end))


let uu___is_DivW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DivW -> begin
true
end
| uu____1209 -> begin
false
end))


let uu___is_Mult : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult -> begin
true
end
| uu____1213 -> begin
false
end))


let uu___is_MultW : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MultW -> begin
true
end
| uu____1217 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____1221 -> begin
false
end))


let uu___is_BOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BOr -> begin
true
end
| uu____1225 -> begin
false
end))


let uu___is_BAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BAnd -> begin
true
end
| uu____1229 -> begin
false
end))


let uu___is_BXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BXor -> begin
true
end
| uu____1233 -> begin
false
end))


let uu___is_BShiftL : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftL -> begin
true
end
| uu____1237 -> begin
false
end))


let uu___is_BShiftR : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BShiftR -> begin
true
end
| uu____1241 -> begin
false
end))


let uu___is_BNot : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BNot -> begin
true
end
| uu____1245 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____1249 -> begin
false
end))


let uu___is_Neq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neq -> begin
true
end
| uu____1253 -> begin
false
end))


let uu___is_Lt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____1257 -> begin
false
end))


let uu___is_Lte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lte -> begin
true
end
| uu____1261 -> begin
false
end))


let uu___is_Gt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____1265 -> begin
false
end))


let uu___is_Gte : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gte -> begin
true
end
| uu____1269 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____1273 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____1277 -> begin
false
end))


let uu___is_Xor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Xor -> begin
true
end
| uu____1281 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____1285 -> begin
false
end))


let uu___is_PUnit : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PUnit -> begin
true
end
| uu____1289 -> begin
false
end))


let uu___is_PBool : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PBool (_0) -> begin
true
end
| uu____1294 -> begin
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
| uu____1306 -> begin
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
| uu____1321 -> begin
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
| uu____1343 -> begin
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
| uu____1361 -> begin
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
| uu____1381 -> begin
false
end))


let uu___is_UInt16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt16 -> begin
true
end
| uu____1385 -> begin
false
end))


let uu___is_UInt32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt32 -> begin
true
end
| uu____1389 -> begin
false
end))


let uu___is_UInt64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt64 -> begin
true
end
| uu____1393 -> begin
false
end))


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____1397 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____1401 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____1405 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____1409 -> begin
false
end))


let uu___is_Bool : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool -> begin
true
end
| uu____1413 -> begin
false
end))


let uu___is_Int : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int -> begin
true
end
| uu____1417 -> begin
false
end))


let uu___is_UInt : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UInt -> begin
true
end
| uu____1421 -> begin
false
end))


let uu___is_TInt : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TInt (_0) -> begin
true
end
| uu____1438 -> begin
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
| uu____1450 -> begin
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
| uu____1461 -> begin
false
end))


let uu___is_TQualified : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TQualified (_0) -> begin
true
end
| uu____1469 -> begin
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
| uu____1489 -> begin
false
end))


let uu___is_TAny : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAny -> begin
true
end
| uu____1493 -> begin
false
end))


let uu___is_TArrow : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TArrow (_0) -> begin
true
end
| uu____1500 -> begin
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
| uu____1517 -> begin
false
end))


let uu___is_TBound : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TBound (_0) -> begin
true
end
| uu____1522 -> begin
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
| uu____1540 -> begin
false
end))


<<<<<<< HEAD
let __proj__TApp__item___0 : typ  ->  ((Prims.string Prims.list * Prims.string) * typ Prims.list) = (fun projectee -> (match (projectee) with
| TApp (_0) -> begin
_0
end))


let uu___is_TTuple : typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TTuple (_0) -> begin
true
end
| uu____1571 -> begin
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
=======
let ___EString____0 = (fun projectee -> (match (projectee) with
| EString (_84_106) -> begin
_84_106
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_84_109) -> begin
_84_109
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_84_112) -> begin
_84_112
end))


let ___PCons____0 = (fun projectee -> (match (projectee) with
| PCons (_84_115) -> begin
_84_115
end))


let ___PTuple____0 = (fun projectee -> (match (projectee) with
| PTuple (_84_118) -> begin
_84_118
end))


let ___PRecord____0 = (fun projectee -> (match (projectee) with
| PRecord (_84_121) -> begin
_84_121
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_84_125) -> begin
_84_125
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_84_128) -> begin
_84_128
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_84_131) -> begin
_84_131
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_84_134) -> begin
_84_134
end))


let ___TBound____0 = (fun projectee -> (match (projectee) with
| TBound (_84_137) -> begin
_84_137
end))


let ___TApp____0 = (fun projectee -> (match (projectee) with
| TApp (_84_140) -> begin
_84_140
end))


let ___TTuple____0 = (fun projectee -> (match (projectee) with
| TTuple (_84_143) -> begin
_84_143
end))
>>>>>>> origin/master


type version =
Prims.int


let current_version : version = (Prims.parse_int "19")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


<<<<<<< HEAD
let fst3 = (fun uu____1624 -> (match (uu____1624) with
| (x, uu____1629, uu____1630) -> begin
=======
let fst3 = (fun _84_149 -> (match (_84_149) with
| (x, _84_146, _84_148) -> begin
>>>>>>> origin/master
x
end))


<<<<<<< HEAD
let snd3 = (fun uu____1644 -> (match (uu____1644) with
| (uu____1648, x, uu____1650) -> begin
=======
let snd3 = (fun _84_155 -> (match (_84_155) with
| (_84_151, x, _84_154) -> begin
>>>>>>> origin/master
x
end))


<<<<<<< HEAD
let thd3 = (fun uu____1664 -> (match (uu____1664) with
| (uu____1668, uu____1669, x) -> begin
=======
let thd3 = (fun _84_161 -> (match (_84_161) with
| (_84_157, _84_159, x) -> begin
>>>>>>> origin/master
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun uu___152_1674 -> (match (uu___152_1674) with
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
<<<<<<< HEAD
| uu____1676 -> begin
=======
| _84_172 -> begin
>>>>>>> origin/master
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun uu___153_1680 -> (match (uu___153_1680) with
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
<<<<<<< HEAD
| uu____1682 -> begin
=======
| _84_180 -> begin
>>>>>>> origin/master
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun uu___154_1690 -> (match (uu___154_1690) with
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
<<<<<<< HEAD
| uu____1692 -> begin
=======
| _84_223 -> begin
>>>>>>> origin/master
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

<<<<<<< HEAD
let uu___159_1759 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = uu___159_1759.names_t; module_name = uu___159_1759.module_name}))
=======
let _84_237 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = _84_237.names_t; module_name = _84_237.module_name}))
>>>>>>> origin/master


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

<<<<<<< HEAD
let uu___160_1766 = env
in {names = uu___160_1766.names; names_t = (x)::env.names_t; module_name = uu___160_1766.module_name}))

=======
let _84_241 = env
in {names = _84_241.names; names_t = (x)::env.names_t; module_name = _84_241.module_name}))
>>>>>>> origin/master

let find_name : env  ->  Prims.string  ->  name = (fun env x -> (

let uu____1773 = (FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)
in (match (uu____1773) with
| Some (name) -> begin
name
end
| None -> begin
(failwith "internal error: name not found")
end)))


<<<<<<< HEAD
let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (find_name env x).mut)
=======
let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _183_735 = (find_name env x)
in _183_735.mut))
>>>>>>> origin/master


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
<<<<<<< HEAD
| uu____1792 -> begin
(failwith (FStar_Util.format1 "Internal error: name not found %s\n" x))
=======
| _84_257 -> begin
(let _183_743 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith _183_743))
>>>>>>> origin/master
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
<<<<<<< HEAD
| uu____1802 -> begin
(failwith (FStar_Util.format1 "Internal error: name not found %s\n" x))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env uu____1832 -> (match (uu____1832) with
| ((name, uu____1838), uu____1839) -> begin
=======
| _84_267 -> begin
(let _183_751 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith _183_751))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _84_280 -> (match (_84_280) with
| ((name, _84_276), _84_279) -> begin
>>>>>>> origin/master
(extend env name false)
end)) env binders))


<<<<<<< HEAD
let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____1930 -> (match (uu____1930) with
=======
let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _84_282 -> (match (_84_282) with
>>>>>>> origin/master
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

<<<<<<< HEAD
let uu____1961 = m
in (match (uu____1961) with
| ((prefix, final), uu____1973, uu____1974) -> begin
=======
let _84_291 = m
in (match (_84_291) with
| ((prefix, final), _84_288, _84_290) -> begin
>>>>>>> origin/master
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
<<<<<<< HEAD
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
Some ((translate_module m));
)
end)
with
| e -> begin
((let _0_618 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _0_618));
None;
)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun uu____1994 -> (match (uu____1994) with
| (module_name, modul, uu____2006) -> begin
=======
(

let _84_301 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _183_785 = (translate_module m)
in Some (_183_785)))
end)
with
| e -> begin
(

let _84_297 = (let _183_787 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _183_787))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _84_307 -> (match (_84_307) with
| (module_name, modul, _84_306) -> begin
>>>>>>> origin/master
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
<<<<<<< HEAD
| uu____2030 -> begin
=======
| _84_314 -> begin
>>>>>>> origin/master
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun uu___155_2038 -> (match (uu___155_2038) with
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
<<<<<<< HEAD
((FStar_Util.print1_warning "Warning: unrecognized attribute %s" a);
None;
)
end
| uu____2042 -> begin
=======
(

let _84_326 = (FStar_Util.print1_warning "Warning: unrecognized attribute %s" a)
in None)
end
| _84_329 -> begin
>>>>>>> origin/master
None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___156_2090 -> (match (uu___156_2090) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
<<<<<<< HEAD
| uu____2091 -> begin
=======
| _84_394 -> begin
>>>>>>> origin/master
false
end)) flags)
in (

let env = (match ((flavor = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(extend env name false)
end
| uu____2093 -> begin
env
end)
in (

<<<<<<< HEAD
let rec find_return_type = (fun uu___157_2097 -> (match (uu___157_2097) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2098, uu____2099, t) -> begin
=======
let rec find_return_type = (fun _84_6 -> (match (_84_6) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_84_400, _84_402, t) -> begin
>>>>>>> origin/master
(find_return_type t)
end
| t -> begin
t
end))
in (

<<<<<<< HEAD
let t = (let _0_619 = (find_return_type t0)
in (translate_type env _0_619))
=======
let t = (let _183_796 = (find_return_type t0)
in (translate_type env _183_796))
>>>>>>> origin/master
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in (

let flags = (translate_flags flags)
<<<<<<< HEAD
in (match (assumed) with
| true -> begin
Some (DExternal ((let _0_620 = (translate_type env t0)
in ((None), (name), (_0_620)))))
end
| uu____2118 -> begin
=======
in if assumed then begin
(let _183_799 = (let _183_798 = (let _183_797 = (translate_type env t0)
in ((None), (name), (_183_797)))
in DExternal (_183_798))
in Some (_183_799))
end else begin
>>>>>>> origin/master
try
(match (()) with
| () -> begin
(

let body = (translate_expr env body)
in Some (DFunction (((None), (flags), (t), (name), (binders), (body)))))
end)
with
| e -> begin
<<<<<<< HEAD
((let _0_621 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) _0_621));
Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort))));
)
=======
(

let _84_416 = (let _183_802 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) _183_802))
in Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort)))))
>>>>>>> origin/master
end
end)))))))))
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2143); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2145; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = uu____2147})::[]) -> begin
=======
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_434); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _84_427; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _84_424})::[]) -> begin
>>>>>>> origin/master
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
<<<<<<< HEAD
((let _0_622 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) _0_622));
Some (DGlobal (((flags), (name), (t), (EAny))));
)
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2178, uu____2179, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2181); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2183; FStar_Extraction_ML_Syntax.mllb_def = uu____2184; FStar_Extraction_ML_Syntax.print_typ = uu____2185})::uu____2186) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
(match (ts) with
| Some (idents, t) -> begin
(let _0_625 = (let _0_623 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _0_623))
in (let _0_624 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _0_625 _0_624)))
=======
(

let _84_447 = (let _183_805 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) _183_805))
in Some (DGlobal (((flags), (name), (t), (EAny)))))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_84_453, _84_455, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_467); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _84_463; FStar_Extraction_ML_Syntax.mllb_def = _84_461; FStar_Extraction_ML_Syntax.print_typ = _84_459})::_84_457) -> begin
(

let _84_473 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _84_480 = (match (ts) with
| Some (idents, t) -> begin
(let _183_808 = (let _183_806 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _183_806))
in (let _183_807 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _183_808 _183_807)))
>>>>>>> origin/master
end
| None -> begin
()
end);
None;
)
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLM_Let (uu____2199) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2201) -> begin
=======
| FStar_Extraction_ML_Syntax.MLM_Let (_84_483) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_84_486) -> begin
>>>>>>> origin/master
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

<<<<<<< HEAD
let env = (FStar_List.fold_left (fun env uu____2233 -> (match (uu____2233) with
| (name, uu____2237) -> begin
=======
let env = (FStar_List.fold_left (fun env _84_503 -> (match (_84_503) with
| (name, _84_502) -> begin
>>>>>>> origin/master
(extend_t env name)
end)) env args)
in (match (assumed) with
| true -> begin
None
<<<<<<< HEAD
end
| uu____2239 -> begin
Some (DTypeAlias ((let _0_626 = (translate_type env t)
in ((name), ((FStar_List.length args)), (_0_626)))))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2245, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
=======
end else begin
(let _183_813 = (let _183_812 = (let _183_811 = (translate_type env t)
in ((name), ((FStar_List.length args)), (_183_811)))
in DTypeAlias (_183_812))
in Some (_183_813))
end))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_506, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
>>>>>>> origin/master
(

let name = ((env.module_name), (name))
in (

<<<<<<< HEAD
let env = (FStar_List.fold_left (fun env uu____2279 -> (match (uu____2279) with
| (name, uu____2283) -> begin
(extend_t env name)
end)) env args)
in Some (DTypeFlat ((let _0_629 = (FStar_List.map (fun uu____2300 -> (match (uu____2300) with
| (f, t) -> begin
(let _0_628 = (let _0_627 = (translate_type env t)
in ((_0_627), (false)))
in ((f), (_0_628)))
end)) fields)
in ((name), ((FStar_List.length args)), (_0_629)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2311, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
=======
let env = (FStar_List.fold_left (fun env _84_521 -> (match (_84_521) with
| (name, _84_520) -> begin
(extend_t env name)
end)) env args)
in (let _183_821 = (let _183_820 = (let _183_819 = (FStar_List.map (fun _84_525 -> (match (_84_525) with
| (f, t) -> begin
(let _183_818 = (let _183_817 = (translate_type env t)
in ((_183_817), (false)))
in ((f), (_183_818)))
end)) fields)
in ((name), ((FStar_List.length args)), (_183_819)))
in DTypeFlat (_183_820))
in Some (_183_821))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_527, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
>>>>>>> origin/master
(

let name = ((env.module_name), (name))
in (

<<<<<<< HEAD
let env = (FStar_List.fold_left (fun env uu____2346 -> (match (uu____2346) with
| (name, uu____2350) -> begin
(extend_t env name)
end)) env args)
in Some (DTypeVariant ((let _0_636 = (FStar_List.mapi (fun i uu____2375 -> (match (uu____2375) with
| (cons, ts) -> begin
(let _0_635 = (FStar_List.mapi (fun j t -> (let _0_634 = (let _0_631 = (FStar_Util.string_of_int i)
in (let _0_630 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "x%s%s" _0_631 _0_630)))
in (let _0_633 = (let _0_632 = (translate_type env t)
in ((_0_632), (false)))
in ((_0_634), (_0_633))))) ts)
in ((cons), (_0_635)))
end)) branches)
in ((name), ((FStar_List.length args)), (_0_636)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____2403, name, _mangled_name, uu____2406, uu____2407))::uu____2408) -> begin
((FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name);
None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
((FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations");
None;
)
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____2430) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____2432) -> begin
=======
let env = (FStar_List.fold_left (fun env _84_542 -> (match (_84_542) with
| (name, _84_541) -> begin
(extend_t env name)
end)) env args)
in (let _183_836 = (let _183_835 = (let _183_834 = (FStar_List.mapi (fun i _84_547 -> (match (_84_547) with
| (cons, ts) -> begin
(let _183_833 = (FStar_List.mapi (fun j t -> (let _183_832 = (let _183_829 = (FStar_Util.string_of_int i)
in (let _183_828 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "x%s%s" _183_829 _183_828)))
in (let _183_831 = (let _183_830 = (translate_type env t)
in ((_183_830), (false)))
in ((_183_832), (_183_831))))) ts)
in ((cons), (_183_833)))
end)) branches)
in ((name), ((FStar_List.length args)), (_183_834)))
in DTypeVariant (_183_835))
in Some (_183_836))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_553, name, _mangled_name, _84_557, _84_559))::_84_551) -> begin
(

let _84_563 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _84_567 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_84_570) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_84_573) -> begin
>>>>>>> origin/master
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLTY_Var (name, uu____2440) -> begin
TBound ((find_t env name))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____2442, t2) -> begin
TArrow ((let _0_638 = (translate_type env t1)
in (let _0_637 = (translate_type env t2)
in ((_0_638), (_0_637)))))
=======
| FStar_Extraction_ML_Syntax.MLTY_Var (name, _84_582) -> begin
(let _183_839 = (find_t env name)
in TBound (_183_839))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _84_587, t2) -> begin
(let _183_842 = (let _183_841 = (translate_type env t1)
in (let _183_840 = (translate_type env t2)
in ((_183_841), (_183_840))))
in TArrow (_183_842))
>>>>>>> origin/master
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
<<<<<<< HEAD
TInt ((FStar_Util.must (mk_width m)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
TInt ((FStar_Util.must (mk_width m)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
TBuf ((translate_type env arg))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((uu____2463)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
=======
(let _183_843 = (FStar_Util.must (mk_width m))
in TInt (_183_843))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(let _183_844 = (FStar_Util.must (mk_width m))
in TInt (_183_844))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _183_845 = (translate_type env arg)
in TBuf (_183_845))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_84_621)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
>>>>>>> origin/master
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (("Prims")::[], t)) when (FStar_Util.starts_with t "tuple") -> begin
<<<<<<< HEAD
TTuple ((FStar_List.map (translate_type env) args))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
TApp ((let _0_639 = (FStar_List.map (translate_type env) args)
in ((lid), (_0_639))))
=======
(let _183_846 = (FStar_List.map (translate_type env) args)
in TTuple (_183_846))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(let _183_848 = (let _183_847 = (FStar_List.map (translate_type env) args)
in ((lid), (_183_847)))
in TApp (_183_848))
end else begin
TQualified (lid)
>>>>>>> origin/master
end
| uu____2491 -> begin
TQualified (lid)
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
<<<<<<< HEAD
TTuple ((FStar_List.map (translate_type env) ts))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env uu____2502 -> (match (uu____2502) with
| ((name, uu____2506), typ) -> begin
(let _0_640 = (translate_type env typ)
in {name = name; typ = _0_640; mut = false})
=======
(let _183_849 = (FStar_List.map (translate_type env) ts)
in TTuple (_183_849))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _84_653 -> (match (_84_653) with
| ((name, _84_650), typ) -> begin
(let _183_854 = (translate_type env typ)
in {name = name; typ = _183_854; mut = false})
>>>>>>> origin/master
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____2514) -> begin
EBound ((find env name))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
EOp ((let _0_642 = (FStar_Util.must (mk_op op))
in (let _0_641 = (FStar_Util.must (mk_width m))
in ((_0_642), (_0_641)))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
EOp ((let _0_643 = (FStar_Util.must (mk_bool_op op))
in ((_0_643), (Bool))))
=======
| FStar_Extraction_ML_Syntax.MLE_Var (name, _84_662) -> begin
(let _183_857 = (find env name)
in EBound (_183_857))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _183_860 = (let _183_859 = (FStar_Util.must (mk_op op))
in (let _183_858 = (FStar_Util.must (mk_width m))
in ((_183_859), (_183_858))))
in EOp (_183_860))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _183_862 = (let _183_861 = (FStar_Util.must (mk_bool_op op))
in ((_183_861), (Bool)))
in EOp (_183_862))
>>>>>>> origin/master
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____2524); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
=======
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_689); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
>>>>>>> origin/master
(

let is_mut = (FStar_Util.for_some (fun uu___158_2540 -> (match (uu___158_2540) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
<<<<<<< HEAD
| uu____2541 -> begin
=======
| _84_700 -> begin
>>>>>>> origin/master
false
end)) flags)
in (

<<<<<<< HEAD
let uu____2542 = (match (is_mut) with
| true -> begin
(let _0_646 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.stackref") -> begin
t
end
| uu____2550 -> begin
(failwith (let _0_644 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _0_644)))
end)
in (let _0_645 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (uu____2552, (body)::[]); FStar_Extraction_ML_Syntax.mlty = uu____2554; FStar_Extraction_ML_Syntax.loc = uu____2555} -> begin
body
end
| uu____2557 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((_0_646), (_0_645))))
end
| uu____2558 -> begin
((typ), (body))
end)
in (match (uu____2542) with
| (typ, body) -> begin
(

let binder = (let _0_647 = (translate_type env typ)
in {name = name; typ = _0_647; mut = is_mut})
=======
let _84_724 = if is_mut then begin
(let _183_867 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.stackref") -> begin
t
end
| _84_708 -> begin
(let _183_865 = (let _183_864 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _183_864))
in (failwith _183_865))
end)
in (let _183_866 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_84_714, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _84_712; FStar_Extraction_ML_Syntax.loc = _84_710} -> begin
body
end
| _84_721 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((_183_867), (_183_866))))
end else begin
((typ), (body))
end
in (match (_84_724) with
| (typ, body) -> begin
(

let binder = (let _183_868 = (translate_type env typ)
in {name = name; typ = _183_868; mut = is_mut})
>>>>>>> origin/master
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
<<<<<<< HEAD
EMatch ((let _0_649 = (translate_expr env expr)
in (let _0_648 = (translate_branches env branches)
in ((_0_649), (_0_648)))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2581; FStar_Extraction_ML_Syntax.loc = uu____2582}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, uu____2584); FStar_Extraction_ML_Syntax.mlty = uu____2585; FStar_Extraction_ML_Syntax.loc = uu____2586})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") && (is_mutable env v)) -> begin
EBound ((find env v))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2589; FStar_Extraction_ML_Syntax.loc = uu____2590}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, uu____2592); FStar_Extraction_ML_Syntax.mlty = uu____2593; FStar_Extraction_ML_Syntax.loc = uu____2594})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") && (is_mutable env v)) -> begin
EAssign ((let _0_651 = EBound ((find env v))
in (let _0_650 = (translate_expr env e)
in ((_0_651), (_0_650)))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2598; FStar_Extraction_ML_Syntax.loc = uu____2599}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
EBufRead ((let _0_653 = (translate_expr env e1)
in (let _0_652 = (translate_expr env e2)
in ((_0_653), (_0_652)))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2604; FStar_Extraction_ML_Syntax.loc = uu____2605}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
EBufCreate ((let _0_655 = (translate_expr env e1)
in (let _0_654 = (translate_expr env e2)
in ((Stack), (_0_655), (_0_654)))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2610; FStar_Extraction_ML_Syntax.loc = uu____2611}, (_e0)::(e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.rcreate") -> begin
EBufCreate ((let _0_657 = (translate_expr env e1)
in (let _0_656 = (translate_expr env e2)
in ((Eternal), (_0_657), (_0_656)))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2617; FStar_Extraction_ML_Syntax.loc = uu____2618}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
=======
(let _183_871 = (let _183_870 = (translate_expr env expr)
in (let _183_869 = (translate_branches env branches)
in ((_183_870), (_183_869))))
in EMatch (_183_871))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_736; FStar_Extraction_ML_Syntax.loc = _84_734}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _84_746); FStar_Extraction_ML_Syntax.mlty = _84_743; FStar_Extraction_ML_Syntax.loc = _84_741})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") && (is_mutable env v)) -> begin
(let _183_872 = (find env v)
in EBound (_183_872))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_756; FStar_Extraction_ML_Syntax.loc = _84_754}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _84_767); FStar_Extraction_ML_Syntax.mlty = _84_764; FStar_Extraction_ML_Syntax.loc = _84_762})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _183_876 = (let _183_875 = (let _183_873 = (find env v)
in EBound (_183_873))
in (let _183_874 = (translate_expr env e)
in ((_183_875), (_183_874))))
in EAssign (_183_876))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_777; FStar_Extraction_ML_Syntax.loc = _84_775}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _183_879 = (let _183_878 = (translate_expr env e1)
in (let _183_877 = (translate_expr env e2)
in ((_183_878), (_183_877))))
in EBufRead (_183_879))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_789; FStar_Extraction_ML_Syntax.loc = _84_787}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _183_882 = (let _183_881 = (translate_expr env e1)
in (let _183_880 = (translate_expr env e2)
in ((Stack), (_183_881), (_183_880))))
in EBufCreate (_183_882))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_801; FStar_Extraction_ML_Syntax.loc = _84_799}, (_e0)::(e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.rcreate") -> begin
(let _183_885 = (let _183_884 = (translate_expr env e1)
in (let _183_883 = (translate_expr env e2)
in ((Eternal), (_183_884), (_183_883))))
in EBufCreate (_183_885))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_814; FStar_Extraction_ML_Syntax.loc = _84_812}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
>>>>>>> origin/master
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
<<<<<<< HEAD
| uu____2644 -> begin
=======
| _84_842 -> begin
>>>>>>> origin/master
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
<<<<<<< HEAD
in EBufCreateL ((let _0_659 = (let _0_658 = (list_elements e2)
in (FStar_List.map (translate_expr env) _0_658))
in ((Stack), (_0_659))))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2652; FStar_Extraction_ML_Syntax.loc = uu____2653}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
EBufSub ((let _0_661 = (translate_expr env e1)
in (let _0_660 = (translate_expr env e2)
in ((_0_661), (_0_660)))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2659; FStar_Extraction_ML_Syntax.loc = uu____2660}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.join") -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2665; FStar_Extraction_ML_Syntax.loc = uu____2666}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
EBufSub ((let _0_663 = (translate_expr env e1)
in (let _0_662 = (translate_expr env e2)
in ((_0_663), (_0_662)))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2671; FStar_Extraction_ML_Syntax.loc = uu____2672}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
EBufWrite ((let _0_666 = (translate_expr env e1)
in (let _0_665 = (translate_expr env e2)
in (let _0_664 = (translate_expr env e3)
in ((_0_666), (_0_665), (_0_664))))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2678; FStar_Extraction_ML_Syntax.loc = uu____2679}, (uu____2680)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2683; FStar_Extraction_ML_Syntax.loc = uu____2684}, (uu____2685)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2688; FStar_Extraction_ML_Syntax.loc = uu____2689}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
EBufBlit ((let _0_671 = (translate_expr env e1)
in (let _0_670 = (translate_expr env e2)
in (let _0_669 = (translate_expr env e3)
in (let _0_668 = (translate_expr env e4)
in (let _0_667 = (translate_expr env e5)
in ((_0_671), (_0_670), (_0_669), (_0_668), (_0_667))))))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2697; FStar_Extraction_ML_Syntax.loc = uu____2698}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.fill") -> begin
EBufFill ((let _0_674 = (translate_expr env e1)
in (let _0_673 = (translate_expr env e2)
in (let _0_672 = (translate_expr env e3)
in ((_0_674), (_0_673), (_0_672))))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2704; FStar_Extraction_ML_Syntax.loc = uu____2705}, (uu____2706)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2709; FStar_Extraction_ML_Syntax.loc = uu____2710}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
ECast ((let _0_675 = (translate_expr env e)
in ((_0_675), (TAny))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = uu____2715; FStar_Extraction_ML_Syntax.loc = uu____2716}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _0_677 = (FStar_Util.must (mk_width m))
in (let _0_676 = (FStar_Util.must (mk_op op))
in (mk_op_app env _0_677 _0_676 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = uu____2722; FStar_Extraction_ML_Syntax.loc = uu____2723}, args) when (is_bool_op op) -> begin
(let _0_678 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _0_678 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
EConstant ((let _0_679 = (FStar_Util.must (mk_width m))
in ((_0_679), (c))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = uu____2753; FStar_Extraction_ML_Syntax.loc = uu____2754}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in (match (((FStar_Util.ends_with c "uint64") && is_known_type)) with
| true -> begin
ECast ((let _0_680 = (translate_expr env arg)
in ((_0_680), (TInt (UInt64)))))
end
| uu____2759 -> begin
(match (((FStar_Util.ends_with c "uint32") && is_known_type)) with
| true -> begin
ECast ((let _0_681 = (translate_expr env arg)
in ((_0_681), (TInt (UInt32)))))
end
| uu____2760 -> begin
(match (((FStar_Util.ends_with c "uint16") && is_known_type)) with
| true -> begin
ECast ((let _0_682 = (translate_expr env arg)
in ((_0_682), (TInt (UInt16)))))
end
| uu____2761 -> begin
(match (((FStar_Util.ends_with c "uint8") && is_known_type)) with
| true -> begin
ECast ((let _0_683 = (translate_expr env arg)
in ((_0_683), (TInt (UInt8)))))
end
| uu____2762 -> begin
(match (((FStar_Util.ends_with c "int64") && is_known_type)) with
| true -> begin
ECast ((let _0_684 = (translate_expr env arg)
in ((_0_684), (TInt (Int64)))))
end
| uu____2763 -> begin
(match (((FStar_Util.ends_with c "int32") && is_known_type)) with
| true -> begin
ECast ((let _0_685 = (translate_expr env arg)
in ((_0_685), (TInt (Int32)))))
end
| uu____2764 -> begin
(match (((FStar_Util.ends_with c "int16") && is_known_type)) with
| true -> begin
ECast ((let _0_686 = (translate_expr env arg)
in ((_0_686), (TInt (Int16)))))
end
| uu____2765 -> begin
(match (((FStar_Util.ends_with c "int8") && is_known_type)) with
| true -> begin
ECast ((let _0_687 = (translate_expr env arg)
in ((_0_687), (TInt (Int8)))))
end
| uu____2766 -> begin
EApp ((let _0_689 = (let _0_688 = (translate_expr env arg)
in (_0_688)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (_0_689))))
end)
end)
end)
=======
in (let _183_893 = (let _183_892 = (let _183_891 = (list_elements e2)
in (FStar_List.map (translate_expr env) _183_891))
in ((Stack), (_183_892)))
in EBufCreateL (_183_893))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_847; FStar_Extraction_ML_Syntax.loc = _84_845}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _183_896 = (let _183_895 = (translate_expr env e1)
in (let _183_894 = (translate_expr env e2)
in ((_183_895), (_183_894))))
in EBufSub (_183_896))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_860; FStar_Extraction_ML_Syntax.loc = _84_858}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.join") -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_872; FStar_Extraction_ML_Syntax.loc = _84_870}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _183_899 = (let _183_898 = (translate_expr env e1)
in (let _183_897 = (translate_expr env e2)
in ((_183_898), (_183_897))))
in EBufSub (_183_899))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_884; FStar_Extraction_ML_Syntax.loc = _84_882}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _183_903 = (let _183_902 = (translate_expr env e1)
in (let _183_901 = (translate_expr env e2)
in (let _183_900 = (translate_expr env e3)
in ((_183_902), (_183_901), (_183_900)))))
in EBufWrite (_183_903))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_897; FStar_Extraction_ML_Syntax.loc = _84_895}, (_84_902)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_909; FStar_Extraction_ML_Syntax.loc = _84_907}, (_84_914)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_921; FStar_Extraction_ML_Syntax.loc = _84_919}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _183_909 = (let _183_908 = (translate_expr env e1)
in (let _183_907 = (translate_expr env e2)
in (let _183_906 = (translate_expr env e3)
in (let _183_905 = (translate_expr env e4)
in (let _183_904 = (translate_expr env e5)
in ((_183_908), (_183_907), (_183_906), (_183_905), (_183_904)))))))
in EBufBlit (_183_909))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_936; FStar_Extraction_ML_Syntax.loc = _84_934}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.fill") -> begin
(let _183_913 = (let _183_912 = (translate_expr env e1)
in (let _183_911 = (translate_expr env e2)
in (let _183_910 = (translate_expr env e3)
in ((_183_912), (_183_911), (_183_910)))))
in EBufFill (_183_913))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_949; FStar_Extraction_ML_Syntax.loc = _84_947}, (_84_954)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_961; FStar_Extraction_ML_Syntax.loc = _84_959}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
(let _183_915 = (let _183_914 = (translate_expr env e)
in ((_183_914), (TAny)))
in ECast (_183_915))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _84_972; FStar_Extraction_ML_Syntax.loc = _84_970}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _183_917 = (FStar_Util.must (mk_width m))
in (let _183_916 = (FStar_Util.must (mk_op op))
in (mk_op_app env _183_917 _183_916 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _84_986; FStar_Extraction_ML_Syntax.loc = _84_984}, args) when (is_bool_op op) -> begin
(let _183_918 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _183_918 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _183_920 = (let _183_919 = (FStar_Util.must (mk_width m))
in ((_183_919), (c)))
in EConstant (_183_920))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("C")::[], "string_of_literal"); FStar_Extraction_ML_Syntax.mlty = _84_1045; FStar_Extraction_ML_Syntax.loc = _84_1043}, ({FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.mlty = _84_1055; FStar_Extraction_ML_Syntax.loc = _84_1053})::[]) -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String (s)) -> begin
EString (s)
end
| _84_1065 -> begin
(failwith "Cannot extract string_of_literal applied to a non-literal")
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _84_1069; FStar_Extraction_ML_Syntax.loc = _84_1067}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in if ((FStar_Util.ends_with c "uint64") && is_known_type) then begin
(let _183_922 = (let _183_921 = (translate_expr env arg)
in ((_183_921), (TInt (UInt64))))
in ECast (_183_922))
end else begin
if ((FStar_Util.ends_with c "uint32") && is_known_type) then begin
(let _183_924 = (let _183_923 = (translate_expr env arg)
in ((_183_923), (TInt (UInt32))))
in ECast (_183_924))
end else begin
if ((FStar_Util.ends_with c "uint16") && is_known_type) then begin
(let _183_926 = (let _183_925 = (translate_expr env arg)
in ((_183_925), (TInt (UInt16))))
in ECast (_183_926))
end else begin
if ((FStar_Util.ends_with c "uint8") && is_known_type) then begin
(let _183_928 = (let _183_927 = (translate_expr env arg)
in ((_183_927), (TInt (UInt8))))
in ECast (_183_928))
end else begin
if ((FStar_Util.ends_with c "int64") && is_known_type) then begin
(let _183_930 = (let _183_929 = (translate_expr env arg)
in ((_183_929), (TInt (Int64))))
in ECast (_183_930))
end else begin
if ((FStar_Util.ends_with c "int32") && is_known_type) then begin
(let _183_932 = (let _183_931 = (translate_expr env arg)
in ((_183_931), (TInt (Int32))))
in ECast (_183_932))
end else begin
if ((FStar_Util.ends_with c "int16") && is_known_type) then begin
(let _183_934 = (let _183_933 = (translate_expr env arg)
in ((_183_933), (TInt (Int16))))
in ECast (_183_934))
end else begin
if ((FStar_Util.ends_with c "int8") && is_known_type) then begin
(let _183_936 = (let _183_935 = (translate_expr env arg)
in ((_183_935), (TInt (Int8))))
in ECast (_183_936))
end else begin
(let _183_939 = (let _183_938 = (let _183_937 = (translate_expr env arg)
in (_183_937)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (_183_938)))
in EApp (_183_939))
end
end
end
end
end
end
end
>>>>>>> origin/master
end)
end)
end)
end)
end))
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = uu____2771; FStar_Extraction_ML_Syntax.loc = uu____2772}, args) -> begin
EApp ((let _0_690 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_0_690))))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
ECast ((let _0_692 = (translate_expr env e)
in (let _0_691 = (translate_type env t_to)
in ((_0_692), (_0_691)))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____2783, fields) -> begin
EFlat ((let _0_695 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _0_694 = (FStar_List.map (fun uu____2800 -> (match (uu____2800) with
| (field, expr) -> begin
(let _0_693 = (translate_expr env expr)
in ((field), (_0_693)))
end)) fields)
in ((_0_695), (_0_694)))))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
EField ((let _0_697 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _0_696 = (translate_expr env e)
in ((_0_697), (_0_696), ((Prims.snd path))))))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____2810) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, uu____2818) -> begin
(failwith (let _0_698 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _0_698)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
ESequence ((FStar_List.map (translate_expr env) seqs))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
ETuple ((FStar_List.map (translate_expr env) es))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((uu____2826, cons), es) -> begin
ECons ((let _0_700 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _0_699 = (FStar_List.map (translate_expr env) es)
in ((_0_700), (cons), (_0_699)))))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____2837) -> begin
(failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
EIfThenElse ((let _0_703 = (translate_expr env e1)
in (let _0_702 = (translate_expr env e2)
in (let _0_701 = (match (e3) with
=======
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _84_1086; FStar_Extraction_ML_Syntax.loc = _84_1084}, args) -> begin
(let _183_941 = (let _183_940 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_183_940)))
in EApp (_183_941))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _183_944 = (let _183_943 = (translate_expr env e)
in (let _183_942 = (translate_type env t_to)
in ((_183_943), (_183_942))))
in ECast (_183_944))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_84_1101, fields) -> begin
(let _183_949 = (let _183_948 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _183_947 = (FStar_List.map (fun _84_1107 -> (match (_84_1107) with
| (field, expr) -> begin
(let _183_946 = (translate_expr env expr)
in ((field), (_183_946)))
end)) fields)
in ((_183_948), (_183_947))))
in EFlat (_183_949))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _183_952 = (let _183_951 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _183_950 = (translate_expr env e)
in ((_183_951), (_183_950), ((Prims.snd path)))))
in EField (_183_952))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_84_1113) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _84_1117) -> begin
(let _183_954 = (let _183_953 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _183_953))
in (failwith _183_954))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _183_955 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_183_955))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let _183_956 = (FStar_List.map (translate_expr env) es)
in ETuple (_183_956))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((_84_1125, cons), es) -> begin
(let _183_959 = (let _183_958 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _183_957 = (FStar_List.map (translate_expr env) es)
in ((_183_958), (cons), (_183_957))))
in ECons (_183_959))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_84_1132) -> begin
(failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(let _183_963 = (let _183_962 = (translate_expr env e1)
in (let _183_961 = (translate_expr env e2)
in (let _183_960 = (match (e3) with
>>>>>>> origin/master
| None -> begin
EUnit
end
| Some (e3) -> begin
(translate_expr env e3)
end)
<<<<<<< HEAD
in ((_0_703), (_0_702), (_0_701))))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____2849) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____2853) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (uu____2861) -> begin
=======
in ((_183_962), (_183_961), (_183_960)))))
in EIfThenElse (_183_963))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_84_1143) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_84_1146) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_84_1149) -> begin
>>>>>>> origin/master
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
<<<<<<< HEAD
(match (((FStar_List.length ts) > (Prims.parse_int "0"))) with
| true -> begin
TApp ((let _0_704 = (FStar_List.map (translate_type env) ts)
in ((lid), (_0_704))))
=======
if ((FStar_List.length ts) > (Prims.parse_int "0")) then begin
(let _183_967 = (let _183_966 = (FStar_List.map (translate_type env) ts)
in ((lid), (_183_966)))
in TApp (_183_967))
end else begin
TQualified (lid)
>>>>>>> origin/master
end
| uu____2875 -> begin
TQualified (lid)
end)
end
<<<<<<< HEAD
| uu____2876 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (pattern * expr) Prims.list = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr)  ->  (pattern * expr) = (fun env uu____2891 -> (match (uu____2891) with
=======
| _84_1158 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _84_1165 -> (match (_84_1165) with
>>>>>>> origin/master
| (pat, guard, expr) -> begin
(match ((guard = None)) with
| true -> begin
(

<<<<<<< HEAD
let uu____2906 = (translate_pat env pat)
in (match (uu____2906) with
| (env, pat) -> begin
(let _0_705 = (translate_expr env expr)
in ((pat), (_0_705)))
=======
let _84_1168 = (translate_pat env pat)
in (match (_84_1168) with
| (env, pat) -> begin
(let _183_972 = (translate_expr env expr)
in ((pat), (_183_972)))
>>>>>>> origin/master
end))
end
| uu____2913 -> begin
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
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____2922) -> begin
=======
| FStar_Extraction_ML_Syntax.MLP_Var (name, _84_1178) -> begin
>>>>>>> origin/master
(

let env = (extend env name false)
in ((env), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env = (extend env "_" false)
in ((env), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLP_CTor ((uu____2925, cons), ps) -> begin
(

let uu____2935 = (FStar_List.fold_left (fun uu____2942 p -> (match (uu____2942) with
| (env, acc) -> begin
(

let uu____2954 = (translate_pat env p)
in (match (uu____2954) with
=======
| FStar_Extraction_ML_Syntax.MLP_CTor ((_84_1185, cons), ps) -> begin
(

let _84_1200 = (FStar_List.fold_left (fun _84_1193 p -> (match (_84_1193) with
| (env, acc) -> begin
(

let _84_1197 = (translate_pat env p)
in (match (_84_1197) with
>>>>>>> origin/master
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
<<<<<<< HEAD
in (match (uu____2935) with
=======
in (match (_84_1200) with
>>>>>>> origin/master
| (env, ps) -> begin
((env), (PCons (((cons), ((FStar_List.rev ps))))))
end))
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLP_Record (uu____2971, ps) -> begin
(

let uu____2981 = (FStar_List.fold_left (fun uu____2994 uu____2995 -> (match (((uu____2994), (uu____2995))) with
| ((env, acc), (field, p)) -> begin
(

let uu____3032 = (translate_pat env p)
in (match (uu____3032) with
=======
| FStar_Extraction_ML_Syntax.MLP_Record (_84_1202, ps) -> begin
(

let _84_1217 = (FStar_List.fold_left (fun _84_1208 _84_1211 -> (match (((_84_1208), (_84_1211))) with
| ((env, acc), (field, p)) -> begin
(

let _84_1214 = (translate_pat env p)
in (match (_84_1214) with
>>>>>>> origin/master
| (env, p) -> begin
((env), ((((field), (p)))::acc))
end))
end)) ((env), ([])) ps)
<<<<<<< HEAD
in (match (uu____2981) with
=======
in (match (_84_1217) with
>>>>>>> origin/master
| (env, ps) -> begin
((env), (PRecord ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

<<<<<<< HEAD
let uu____3066 = (FStar_List.fold_left (fun uu____3073 p -> (match (uu____3073) with
| (env, acc) -> begin
(

let uu____3085 = (translate_pat env p)
in (match (uu____3085) with
=======
let _84_1229 = (FStar_List.fold_left (fun _84_1222 p -> (match (_84_1222) with
| (env, acc) -> begin
(

let _84_1226 = (translate_pat env p)
in (match (_84_1226) with
>>>>>>> origin/master
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
<<<<<<< HEAD
in (match (uu____3066) with
=======
in (match (_84_1229) with
>>>>>>> origin/master
| (env, ps) -> begin
((env), (PTuple ((FStar_List.rev ps))))
end))
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLP_Const (uu____3101) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (uu____3104) -> begin
=======
| FStar_Extraction_ML_Syntax.MLP_Const (_84_1231) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_84_1234) -> begin
>>>>>>> origin/master
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
<<<<<<< HEAD
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (uu____3111)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (uu____3119) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____3120) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (uu____3121) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____3122) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (uu____3124, None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> EApp ((let _0_706 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_0_706)))))
=======
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_84_1242)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_84_1247) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_84_1250) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_84_1253) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_84_1256) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_84_1259, None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _183_987 = (let _183_986 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_183_986)))
in EApp (_183_987)))
>>>>>>> origin/master




