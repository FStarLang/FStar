
open Prims

type decl =
| DGlobal of (flag Prims.list * lident * typ * expr)
| DFunction of (cc Prims.option * flag Prims.list * typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * Prims.int * typ)
| DTypeFlat of (lident * Prims.int * fields_t)
| DExternal of (cc Prims.option * lident * typ)
| DTypeVariant of (lident * Prims.int * branches_t) 
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
| EBound of var
| EQualified of lident
| EConstant of constant
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
| EMatch of (expr * branches)
| EOp of (op * width)
| ECast of (expr * typ)
| EPushFrame
| EPopFrame
| EBool of Prims.bool
| EAny
| EAbort
| EReturn of expr
| EFlat of (typ * (ident * expr) Prims.list)
| EField of (typ * expr * ident)
| EWhile of (expr * expr)
| EBufCreateL of (lifetime * expr Prims.list)
| ETuple of expr Prims.list
| ECons of (typ * ident * expr Prims.list)
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
| PCons of (ident * pattern Prims.list)
| PTuple of pattern Prims.list
| PRecord of (ident * pattern) Prims.list 
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
{name : ident; typ : typ; mut : Prims.bool} 
 and typ =
| TInt of width
| TBuf of typ
| TUnit
| TQualified of lident
| TBool
| TAny
| TArrow of (typ * typ)
| TZ
| TBound of Prims.int
| TApp of (lident * typ Prims.list)
| TTuple of typ Prims.list 
 and program =
decl Prims.list 
 and fields_t =
(ident * (typ * Prims.bool)) Prims.list 
 and branches_t =
(ident * fields_t) Prims.list 
 and branches =
branch Prims.list 
 and branch =
(pattern * expr) 
 and constant =
(width * Prims.string) 
 and var =
Prims.int 
 and ident =
Prims.string 
 and lident =
(ident Prims.list * ident)


let is_DGlobal = (fun _discr_ -> (match (_discr_) with
| DGlobal (_) -> begin
true
end
| _ -> begin
false
end))


let is_DFunction = (fun _discr_ -> (match (_discr_) with
| DFunction (_) -> begin
true
end
| _ -> begin
false
end))


let is_DTypeAlias = (fun _discr_ -> (match (_discr_) with
| DTypeAlias (_) -> begin
true
end
| _ -> begin
false
end))


let is_DTypeFlat = (fun _discr_ -> (match (_discr_) with
| DTypeFlat (_) -> begin
true
end
| _ -> begin
false
end))


let is_DExternal = (fun _discr_ -> (match (_discr_) with
| DExternal (_) -> begin
true
end
| _ -> begin
false
end))


let is_DTypeVariant = (fun _discr_ -> (match (_discr_) with
| DTypeVariant (_) -> begin
true
end
| _ -> begin
false
end))


let is_StdCall = (fun _discr_ -> (match (_discr_) with
| StdCall (_) -> begin
true
end
| _ -> begin
false
end))


let is_CDecl = (fun _discr_ -> (match (_discr_) with
| CDecl (_) -> begin
true
end
| _ -> begin
false
end))


let is_FastCall = (fun _discr_ -> (match (_discr_) with
| FastCall (_) -> begin
true
end
| _ -> begin
false
end))


let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoExtract = (fun _discr_ -> (match (_discr_) with
| NoExtract (_) -> begin
true
end
| _ -> begin
false
end))


let is_CInline = (fun _discr_ -> (match (_discr_) with
| CInline (_) -> begin
true
end
| _ -> begin
false
end))


let is_Substitute = (fun _discr_ -> (match (_discr_) with
| Substitute (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eternal = (fun _discr_ -> (match (_discr_) with
| Eternal (_) -> begin
true
end
| _ -> begin
false
end))


let is_Stack = (fun _discr_ -> (match (_discr_) with
| Stack (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBound = (fun _discr_ -> (match (_discr_) with
| EBound (_) -> begin
true
end
| _ -> begin
false
end))


let is_EQualified = (fun _discr_ -> (match (_discr_) with
| EQualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_EConstant = (fun _discr_ -> (match (_discr_) with
| EConstant (_) -> begin
true
end
| _ -> begin
false
end))


let is_EUnit = (fun _discr_ -> (match (_discr_) with
| EUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_EApp = (fun _discr_ -> (match (_discr_) with
| EApp (_) -> begin
true
end
| _ -> begin
false
end))


let is_ELet = (fun _discr_ -> (match (_discr_) with
| ELet (_) -> begin
true
end
| _ -> begin
false
end))


let is_EIfThenElse = (fun _discr_ -> (match (_discr_) with
| EIfThenElse (_) -> begin
true
end
| _ -> begin
false
end))


let is_ESequence = (fun _discr_ -> (match (_discr_) with
| ESequence (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAssign = (fun _discr_ -> (match (_discr_) with
| EAssign (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufCreate = (fun _discr_ -> (match (_discr_) with
| EBufCreate (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufRead = (fun _discr_ -> (match (_discr_) with
| EBufRead (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufWrite = (fun _discr_ -> (match (_discr_) with
| EBufWrite (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufSub = (fun _discr_ -> (match (_discr_) with
| EBufSub (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufBlit = (fun _discr_ -> (match (_discr_) with
| EBufBlit (_) -> begin
true
end
| _ -> begin
false
end))


let is_EMatch = (fun _discr_ -> (match (_discr_) with
| EMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_EOp = (fun _discr_ -> (match (_discr_) with
| EOp (_) -> begin
true
end
| _ -> begin
false
end))


let is_ECast = (fun _discr_ -> (match (_discr_) with
| ECast (_) -> begin
true
end
| _ -> begin
false
end))


let is_EPushFrame = (fun _discr_ -> (match (_discr_) with
| EPushFrame (_) -> begin
true
end
| _ -> begin
false
end))


let is_EPopFrame = (fun _discr_ -> (match (_discr_) with
| EPopFrame (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBool = (fun _discr_ -> (match (_discr_) with
| EBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAny = (fun _discr_ -> (match (_discr_) with
| EAny (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAbort = (fun _discr_ -> (match (_discr_) with
| EAbort (_) -> begin
true
end
| _ -> begin
false
end))


let is_EReturn = (fun _discr_ -> (match (_discr_) with
| EReturn (_) -> begin
true
end
| _ -> begin
false
end))


let is_EFlat = (fun _discr_ -> (match (_discr_) with
| EFlat (_) -> begin
true
end
| _ -> begin
false
end))


let is_EField = (fun _discr_ -> (match (_discr_) with
| EField (_) -> begin
true
end
| _ -> begin
false
end))


let is_EWhile = (fun _discr_ -> (match (_discr_) with
| EWhile (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufCreateL = (fun _discr_ -> (match (_discr_) with
| EBufCreateL (_) -> begin
true
end
| _ -> begin
false
end))


let is_ETuple = (fun _discr_ -> (match (_discr_) with
| ETuple (_) -> begin
true
end
| _ -> begin
false
end))


let is_ECons = (fun _discr_ -> (match (_discr_) with
| ECons (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufFill = (fun _discr_ -> (match (_discr_) with
| EBufFill (_) -> begin
true
end
| _ -> begin
false
end))


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
end))


let is_AddW = (fun _discr_ -> (match (_discr_) with
| AddW (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))


let is_SubW = (fun _discr_ -> (match (_discr_) with
| SubW (_) -> begin
true
end
| _ -> begin
false
end))


let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))


let is_DivW = (fun _discr_ -> (match (_discr_) with
| DivW (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mult = (fun _discr_ -> (match (_discr_) with
| Mult (_) -> begin
true
end
| _ -> begin
false
end))


let is_MultW = (fun _discr_ -> (match (_discr_) with
| MultW (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))


let is_BOr = (fun _discr_ -> (match (_discr_) with
| BOr (_) -> begin
true
end
| _ -> begin
false
end))


let is_BAnd = (fun _discr_ -> (match (_discr_) with
| BAnd (_) -> begin
true
end
| _ -> begin
false
end))


let is_BXor = (fun _discr_ -> (match (_discr_) with
| BXor (_) -> begin
true
end
| _ -> begin
false
end))


let is_BShiftL = (fun _discr_ -> (match (_discr_) with
| BShiftL (_) -> begin
true
end
| _ -> begin
false
end))


let is_BShiftR = (fun _discr_ -> (match (_discr_) with
| BShiftR (_) -> begin
true
end
| _ -> begin
false
end))


let is_BNot = (fun _discr_ -> (match (_discr_) with
| BNot (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))


let is_Neq = (fun _discr_ -> (match (_discr_) with
| Neq (_) -> begin
true
end
| _ -> begin
false
end))


let is_Lt = (fun _discr_ -> (match (_discr_) with
| Lt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Lte = (fun _discr_ -> (match (_discr_) with
| Lte (_) -> begin
true
end
| _ -> begin
false
end))


let is_Gt = (fun _discr_ -> (match (_discr_) with
| Gt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Gte = (fun _discr_ -> (match (_discr_) with
| Gte (_) -> begin
true
end
| _ -> begin
false
end))


let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))


let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))


let is_Xor = (fun _discr_ -> (match (_discr_) with
| Xor (_) -> begin
true
end
| _ -> begin
false
end))


let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))


let is_PUnit = (fun _discr_ -> (match (_discr_) with
| PUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_PBool = (fun _discr_ -> (match (_discr_) with
| PBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_PVar = (fun _discr_ -> (match (_discr_) with
| PVar (_) -> begin
true
end
| _ -> begin
false
end))


let is_PCons = (fun _discr_ -> (match (_discr_) with
| PCons (_) -> begin
true
end
| _ -> begin
false
end))


let is_PTuple = (fun _discr_ -> (match (_discr_) with
| PTuple (_) -> begin
true
end
| _ -> begin
false
end))


let is_PRecord = (fun _discr_ -> (match (_discr_) with
| PRecord (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt8 = (fun _discr_ -> (match (_discr_) with
| UInt8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt16 = (fun _discr_ -> (match (_discr_) with
| UInt16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt32 = (fun _discr_ -> (match (_discr_) with
| UInt32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt64 = (fun _discr_ -> (match (_discr_) with
| UInt64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int8 = (fun _discr_ -> (match (_discr_) with
| Int8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int16 = (fun _discr_ -> (match (_discr_) with
| Int16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int32 = (fun _discr_ -> (match (_discr_) with
| Int32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int64 = (fun _discr_ -> (match (_discr_) with
| Int64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Bool = (fun _discr_ -> (match (_discr_) with
| Bool (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int = (fun _discr_ -> (match (_discr_) with
| Int (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt = (fun _discr_ -> (match (_discr_) with
| UInt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkbinder"))))


let is_TInt = (fun _discr_ -> (match (_discr_) with
| TInt (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBuf = (fun _discr_ -> (match (_discr_) with
| TBuf (_) -> begin
true
end
| _ -> begin
false
end))


let is_TUnit = (fun _discr_ -> (match (_discr_) with
| TUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_TQualified = (fun _discr_ -> (match (_discr_) with
| TQualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBool = (fun _discr_ -> (match (_discr_) with
| TBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_TAny = (fun _discr_ -> (match (_discr_) with
| TAny (_) -> begin
true
end
| _ -> begin
false
end))


let is_TArrow = (fun _discr_ -> (match (_discr_) with
| TArrow (_) -> begin
true
end
| _ -> begin
false
end))


let is_TZ = (fun _discr_ -> (match (_discr_) with
| TZ (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBound = (fun _discr_ -> (match (_discr_) with
| TBound (_) -> begin
true
end
| _ -> begin
false
end))


let is_TApp = (fun _discr_ -> (match (_discr_) with
| TApp (_) -> begin
true
end
| _ -> begin
false
end))


let is_TTuple = (fun _discr_ -> (match (_discr_) with
| TTuple (_) -> begin
true
end
| _ -> begin
false
end))


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_84_13) -> begin
_84_13
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_84_16) -> begin
_84_16
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_84_19) -> begin
_84_19
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_84_22) -> begin
_84_22
end))


let ___DExternal____0 = (fun projectee -> (match (projectee) with
| DExternal (_84_25) -> begin
_84_25
end))


let ___DTypeVariant____0 = (fun projectee -> (match (projectee) with
| DTypeVariant (_84_28) -> begin
_84_28
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_84_31) -> begin
_84_31
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_84_34) -> begin
_84_34
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_84_37) -> begin
_84_37
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_84_40) -> begin
_84_40
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_84_43) -> begin
_84_43
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_84_46) -> begin
_84_46
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_84_49) -> begin
_84_49
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_84_52) -> begin
_84_52
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_84_55) -> begin
_84_55
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_84_58) -> begin
_84_58
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_84_61) -> begin
_84_61
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_84_64) -> begin
_84_64
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_84_67) -> begin
_84_67
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_84_70) -> begin
_84_70
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_84_73) -> begin
_84_73
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_84_76) -> begin
_84_76
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_84_79) -> begin
_84_79
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_84_82) -> begin
_84_82
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_84_85) -> begin
_84_85
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_84_88) -> begin
_84_88
end))


let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_84_91) -> begin
_84_91
end))


let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_84_94) -> begin
_84_94
end))


let ___ETuple____0 = (fun projectee -> (match (projectee) with
| ETuple (_84_97) -> begin
_84_97
end))


let ___ECons____0 = (fun projectee -> (match (projectee) with
| ECons (_84_100) -> begin
_84_100
end))


let ___EBufFill____0 = (fun projectee -> (match (projectee) with
| EBufFill (_84_103) -> begin
_84_103
end))


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


type version =
Prims.int


let current_version : version = (Prims.parse_int "19")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _84_149 -> (match (_84_149) with
| (x, _84_146, _84_148) -> begin
x
end))


let snd3 = (fun _84_155 -> (match (_84_155) with
| (_84_151, x, _84_154) -> begin
x
end))


let thd3 = (fun _84_161 -> (match (_84_161) with
| (_84_157, _84_159, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun _84_1 -> (match (_84_1) with
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
| _84_172 -> begin
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun _84_2 -> (match (_84_2) with
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
| _84_180 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun _84_3 -> (match (_84_3) with
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
| _84_223 -> begin
None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))


type env =
{names : name Prims.list; names_t : Prims.string Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; names_t = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _84_237 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = _84_237.names_t; module_name = _84_237.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let _84_241 = env
in {names = _84_241.names; names_t = (x)::env.names_t; module_name = _84_241.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _183_735 = (find_name env x)
in _183_735.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _84_257 -> begin
(let _183_743 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith _183_743))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| _84_267 -> begin
(let _183_751 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith _183_751))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _84_280 -> (match (_84_280) with
| ((name, _84_276), _84_279) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _84_282 -> (match (_84_282) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _84_291 = m
in (match (_84_291) with
| ((prefix, final), _84_288, _84_290) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
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
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _84_314 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun _84_4 -> (match (_84_4) with
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
(

let _84_326 = (FStar_Util.print1_warning "Warning: unrecognized attribute %s" a)
in None)
end
| _84_329 -> begin
None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun _84_5 -> (match (_84_5) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| _84_394 -> begin
false
end)) flags)
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _84_6 -> (match (_84_6) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_84_400, _84_402, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _183_796 = (find_return_type t0)
in (translate_type env _183_796))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in (

let flags = (translate_flags flags)
in if assumed then begin
(let _183_799 = (let _183_798 = (let _183_797 = (translate_type env t0)
in ((None), (name), (_183_797)))
in DExternal (_183_798))
in Some (_183_799))
end else begin
try
(match (()) with
| () -> begin
(

let body = (translate_expr env body)
in Some (DFunction (((None), (flags), (t), (name), (binders), (body)))))
end)
with
| e -> begin
(

let _84_416 = (let _183_802 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) _183_802))
in Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort)))))
end
end))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_434); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _84_427; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _84_424})::[]) -> begin
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
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_84_483) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_84_486) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _84_503 -> (match (_84_503) with
| (name, _84_502) -> begin
(extend_t env name)
end)) env args)
in if assumed then begin
None
end else begin
(let _183_813 = (let _183_812 = (let _183_811 = (translate_type env t)
in ((name), ((FStar_List.length args)), (_183_811)))
in DTypeAlias (_183_812))
in Some (_183_813))
end))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_506, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

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
(

let name = ((env.module_name), (name))
in (

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
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, _84_582) -> begin
(let _183_839 = (find_t env name)
in TBound (_183_839))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _84_587, t2) -> begin
(let _183_842 = (let _183_841 = (translate_type env t1)
in (let _183_840 = (translate_type env t2)
in ((_183_841), (_183_840))))
in TArrow (_183_842))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
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
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (("Prims")::[], t)) when (FStar_Util.starts_with t "tuple") -> begin
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
end
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _183_849 = (FStar_List.map (translate_type env) ts)
in TTuple (_183_849))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _84_653 -> (match (_84_653) with
| ((name, _84_650), typ) -> begin
(let _183_854 = (translate_type env typ)
in {name = name; typ = _183_854; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
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
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_689); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun _84_7 -> (match (_84_7) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| _84_700 -> begin
false
end)) flags)
in (

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
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _84_842 -> begin
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
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
end)
end
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
| None -> begin
EUnit
end
| Some (e3) -> begin
(translate_expr env e3)
end)
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
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
if ((FStar_List.length ts) > (Prims.parse_int "0")) then begin
(let _183_967 = (let _183_966 = (FStar_List.map (translate_type env) ts)
in ((lid), (_183_966)))
in TApp (_183_967))
end else begin
TQualified (lid)
end
end
| _84_1158 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _84_1165 -> (match (_84_1165) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _84_1168 = (translate_pat env pat)
in (match (_84_1168) with
| (env, pat) -> begin
(let _183_972 = (translate_expr env expr)
in ((pat), (_183_972)))
end))
end else begin
(failwith "todo: translate_branch")
end
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  (env * pattern) = (fun env p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
((env), (PUnit))
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (b)) -> begin
((env), (PBool (b)))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name, _84_1178) -> begin
(

let env = (extend env name false)
in ((env), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env = (extend env "_" false)
in ((env), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((_84_1185, cons), ps) -> begin
(

let _84_1200 = (FStar_List.fold_left (fun _84_1193 p -> (match (_84_1193) with
| (env, acc) -> begin
(

let _84_1197 = (translate_pat env p)
in (match (_84_1197) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_84_1200) with
| (env, ps) -> begin
((env), (PCons (((cons), ((FStar_List.rev ps))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (_84_1202, ps) -> begin
(

let _84_1217 = (FStar_List.fold_left (fun _84_1208 _84_1211 -> (match (((_84_1208), (_84_1211))) with
| ((env, acc), (field, p)) -> begin
(

let _84_1214 = (translate_pat env p)
in (match (_84_1214) with
| (env, p) -> begin
((env), ((((field), (p)))::acc))
end))
end)) ((env), ([])) ps)
in (match (_84_1217) with
| (env, ps) -> begin
((env), (PRecord ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let _84_1229 = (FStar_List.fold_left (fun _84_1222 p -> (match (_84_1222) with
| (env, acc) -> begin
(

let _84_1226 = (translate_pat env p)
in (match (_84_1226) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_84_1229) with
| (env, ps) -> begin
((env), (PTuple ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (_84_1231) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_84_1234) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
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




