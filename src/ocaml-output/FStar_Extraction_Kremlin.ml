
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
| DGlobal (_86_13) -> begin
_86_13
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_86_16) -> begin
_86_16
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_86_19) -> begin
_86_19
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_86_22) -> begin
_86_22
end))


let ___DExternal____0 = (fun projectee -> (match (projectee) with
| DExternal (_86_25) -> begin
_86_25
end))


let ___DTypeVariant____0 = (fun projectee -> (match (projectee) with
| DTypeVariant (_86_28) -> begin
_86_28
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_86_31) -> begin
_86_31
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_86_34) -> begin
_86_34
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_86_37) -> begin
_86_37
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_86_40) -> begin
_86_40
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_86_43) -> begin
_86_43
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_86_46) -> begin
_86_46
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_86_49) -> begin
_86_49
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_86_52) -> begin
_86_52
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_86_55) -> begin
_86_55
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_86_58) -> begin
_86_58
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_86_61) -> begin
_86_61
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_86_64) -> begin
_86_64
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_86_67) -> begin
_86_67
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_86_70) -> begin
_86_70
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_86_73) -> begin
_86_73
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_86_76) -> begin
_86_76
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_86_79) -> begin
_86_79
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_86_82) -> begin
_86_82
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_86_85) -> begin
_86_85
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_86_88) -> begin
_86_88
end))


let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_86_91) -> begin
_86_91
end))


let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_86_94) -> begin
_86_94
end))


let ___ETuple____0 = (fun projectee -> (match (projectee) with
| ETuple (_86_97) -> begin
_86_97
end))


let ___ECons____0 = (fun projectee -> (match (projectee) with
| ECons (_86_100) -> begin
_86_100
end))


let ___EBufFill____0 = (fun projectee -> (match (projectee) with
| EBufFill (_86_103) -> begin
_86_103
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_86_106) -> begin
_86_106
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_86_109) -> begin
_86_109
end))


let ___PCons____0 = (fun projectee -> (match (projectee) with
| PCons (_86_112) -> begin
_86_112
end))


let ___PTuple____0 = (fun projectee -> (match (projectee) with
| PTuple (_86_115) -> begin
_86_115
end))


let ___PRecord____0 = (fun projectee -> (match (projectee) with
| PRecord (_86_118) -> begin
_86_118
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_86_122) -> begin
_86_122
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_86_125) -> begin
_86_125
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_86_128) -> begin
_86_128
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_86_131) -> begin
_86_131
end))


let ___TBound____0 = (fun projectee -> (match (projectee) with
| TBound (_86_134) -> begin
_86_134
end))


let ___TApp____0 = (fun projectee -> (match (projectee) with
| TApp (_86_137) -> begin
_86_137
end))


let ___TTuple____0 = (fun projectee -> (match (projectee) with
| TTuple (_86_140) -> begin
_86_140
end))


type version =
Prims.int


let current_version : version = (Prims.parse_int "19")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _86_146 -> (match (_86_146) with
| (x, _86_143, _86_145) -> begin
x
end))


let snd3 = (fun _86_152 -> (match (_86_152) with
| (_86_148, x, _86_151) -> begin
x
end))


let thd3 = (fun _86_158 -> (match (_86_158) with
| (_86_154, _86_156, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun _86_1 -> (match (_86_1) with
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
| _86_169 -> begin
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun _86_2 -> (match (_86_2) with
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
| _86_177 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun _86_3 -> (match (_86_3) with
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
| _86_220 -> begin
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

let _86_234 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = _86_234.names_t; module_name = _86_234.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let _86_238 = env
in {names = _86_238.names; names_t = (x)::env.names_t; module_name = _86_238.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _186_721 = (find_name env x)
in _186_721.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _86_254 -> begin
(let _186_729 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith _186_729))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| _86_264 -> begin
(let _186_737 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (failwith _186_737))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _86_277 -> (match (_86_277) with
| ((name, _86_273), _86_276) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _86_279 -> (match (_86_279) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _86_288 = m
in (match (_86_288) with
| ((prefix, final), _86_285, _86_287) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _86_298 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _186_771 = (translate_module m)
in Some (_186_771)))
end)
with
| e -> begin
(

let _86_294 = (let _186_773 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _186_773))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _86_304 -> (match (_86_304) with
| (module_name, modul, _86_303) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _86_311 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun _86_4 -> (match (_86_4) with
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

let _86_323 = (FStar_Util.print1_warning "Warning: unrecognized attribute %s" a)
in None)
end
| _86_326 -> begin
None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun _86_5 -> (match (_86_5) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| _86_391 -> begin
false
end)) flags)
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _86_6 -> (match (_86_6) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_86_397, _86_399, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _186_782 = (find_return_type t0)
in (translate_type env _186_782))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in (

let flags = (translate_flags flags)
in if assumed then begin
(let _186_785 = (let _186_784 = (let _186_783 = (translate_type env t0)
in ((None), (name), (_186_783)))
in DExternal (_186_784))
in Some (_186_785))
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

let _86_413 = (let _186_788 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) _186_788))
in Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort)))))
end
end))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _86_431); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _86_424; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _86_421})::[]) -> begin
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

let _86_444 = (let _186_791 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) _186_791))
in Some (DGlobal (((flags), (name), (t), (EAny)))))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_86_450, _86_452, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _86_464); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _86_460; FStar_Extraction_ML_Syntax.mllb_def = _86_458; FStar_Extraction_ML_Syntax.print_typ = _86_456})::_86_454) -> begin
(

let _86_470 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _86_477 = (match (ts) with
| Some (idents, t) -> begin
(let _186_794 = (let _186_792 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _186_792))
in (let _186_793 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _186_794 _186_793)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_86_480) -> begin
(failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_86_483) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _86_500 -> (match (_86_500) with
| (name, _86_499) -> begin
(extend_t env name)
end)) env args)
in if assumed then begin
None
end else begin
(let _186_799 = (let _186_798 = (let _186_797 = (translate_type env t)
in ((name), ((FStar_List.length args)), (_186_797)))
in DTypeAlias (_186_798))
in Some (_186_799))
end))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_86_503, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _86_518 -> (match (_86_518) with
| (name, _86_517) -> begin
(extend_t env name)
end)) env args)
in (let _186_807 = (let _186_806 = (let _186_805 = (FStar_List.map (fun _86_522 -> (match (_86_522) with
| (f, t) -> begin
(let _186_804 = (let _186_803 = (translate_type env t)
in ((_186_803), (false)))
in ((f), (_186_804)))
end)) fields)
in ((name), ((FStar_List.length args)), (_186_805)))
in DTypeFlat (_186_806))
in Some (_186_807))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_86_524, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _86_539 -> (match (_86_539) with
| (name, _86_538) -> begin
(extend_t env name)
end)) env args)
in (let _186_822 = (let _186_821 = (let _186_820 = (FStar_List.mapi (fun i _86_544 -> (match (_86_544) with
| (cons, ts) -> begin
(let _186_819 = (FStar_List.mapi (fun j t -> (let _186_818 = (let _186_815 = (FStar_Util.string_of_int i)
in (let _186_814 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "x%s%s" _186_815 _186_814)))
in (let _186_817 = (let _186_816 = (translate_type env t)
in ((_186_816), (false)))
in ((_186_818), (_186_817))))) ts)
in ((cons), (_186_819)))
end)) branches)
in ((name), ((FStar_List.length args)), (_186_820)))
in DTypeVariant (_186_821))
in Some (_186_822))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_86_550, name, _mangled_name, _86_554, _86_556))::_86_548) -> begin
(

let _86_560 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _86_564 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_86_567) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_86_570) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, _86_579) -> begin
(let _186_825 = (find_t env name)
in TBound (_186_825))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _86_584, t2) -> begin
(let _186_828 = (let _186_827 = (translate_type env t1)
in (let _186_826 = (translate_type env t2)
in ((_186_827), (_186_826))))
in TArrow (_186_828))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(let _186_829 = (FStar_Util.must (mk_width m))
in TInt (_186_829))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(let _186_830 = (FStar_Util.must (mk_width m))
in TInt (_186_830))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _186_831 = (translate_type env arg)
in TBuf (_186_831))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_86_618)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (("Prims")::[], t)) when (FStar_Util.starts_with t "tuple") -> begin
(let _186_832 = (FStar_List.map (translate_type env) args)
in TTuple (_186_832))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(let _186_834 = (let _186_833 = (FStar_List.map (translate_type env) args)
in ((lid), (_186_833)))
in TApp (_186_834))
end else begin
TQualified (lid)
end
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _186_835 = (FStar_List.map (translate_type env) ts)
in TTuple (_186_835))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _86_650 -> (match (_86_650) with
| ((name, _86_647), typ) -> begin
(let _186_840 = (translate_type env typ)
in {name = name; typ = _186_840; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _86_659) -> begin
(let _186_843 = (find env name)
in EBound (_186_843))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _186_846 = (let _186_845 = (FStar_Util.must (mk_op op))
in (let _186_844 = (FStar_Util.must (mk_width m))
in ((_186_845), (_186_844))))
in EOp (_186_846))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _186_848 = (let _186_847 = (FStar_Util.must (mk_bool_op op))
in ((_186_847), (Bool)))
in EOp (_186_848))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _86_686); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun _86_7 -> (match (_86_7) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| _86_697 -> begin
false
end)) flags)
in (

let _86_721 = if is_mut then begin
(let _186_853 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.stackref") -> begin
t
end
| _86_705 -> begin
(let _186_851 = (let _186_850 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _186_850))
in (failwith _186_851))
end)
in (let _186_852 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_86_711, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _86_709; FStar_Extraction_ML_Syntax.loc = _86_707} -> begin
body
end
| _86_718 -> begin
(failwith "unexpected: bad desugaring of Mutable")
end)
in ((_186_853), (_186_852))))
end else begin
((typ), (body))
end
in (match (_86_721) with
| (typ, body) -> begin
(

let binder = (let _186_854 = (translate_type env typ)
in {name = name; typ = _186_854; mut = is_mut})
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
(let _186_857 = (let _186_856 = (translate_expr env expr)
in (let _186_855 = (translate_branches env branches)
in ((_186_856), (_186_855))))
in EMatch (_186_857))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_733; FStar_Extraction_ML_Syntax.loc = _86_731}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _86_743); FStar_Extraction_ML_Syntax.mlty = _86_740; FStar_Extraction_ML_Syntax.loc = _86_738})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") && (is_mutable env v)) -> begin
(let _186_858 = (find env v)
in EBound (_186_858))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_753; FStar_Extraction_ML_Syntax.loc = _86_751}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _86_764); FStar_Extraction_ML_Syntax.mlty = _86_761; FStar_Extraction_ML_Syntax.loc = _86_759})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _186_862 = (let _186_861 = (let _186_859 = (find env v)
in EBound (_186_859))
in (let _186_860 = (translate_expr env e)
in ((_186_861), (_186_860))))
in EAssign (_186_862))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_774; FStar_Extraction_ML_Syntax.loc = _86_772}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _186_865 = (let _186_864 = (translate_expr env e1)
in (let _186_863 = (translate_expr env e2)
in ((_186_864), (_186_863))))
in EBufRead (_186_865))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_786; FStar_Extraction_ML_Syntax.loc = _86_784}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _186_868 = (let _186_867 = (translate_expr env e1)
in (let _186_866 = (translate_expr env e2)
in ((Stack), (_186_867), (_186_866))))
in EBufCreate (_186_868))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_798; FStar_Extraction_ML_Syntax.loc = _86_796}, (_e0)::(e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.rcreate") -> begin
(let _186_871 = (let _186_870 = (translate_expr env e1)
in (let _186_869 = (translate_expr env e2)
in ((Eternal), (_186_870), (_186_869))))
in EBufCreate (_186_871))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_811; FStar_Extraction_ML_Syntax.loc = _86_809}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _86_839 -> begin
(failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (let _186_879 = (let _186_878 = (let _186_877 = (list_elements e2)
in (FStar_List.map (translate_expr env) _186_877))
in ((Stack), (_186_878)))
in EBufCreateL (_186_879))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_844; FStar_Extraction_ML_Syntax.loc = _86_842}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _186_882 = (let _186_881 = (translate_expr env e1)
in (let _186_880 = (translate_expr env e2)
in ((_186_881), (_186_880))))
in EBufSub (_186_882))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_857; FStar_Extraction_ML_Syntax.loc = _86_855}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.join") -> begin
(translate_expr env e1)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_869; FStar_Extraction_ML_Syntax.loc = _86_867}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _186_885 = (let _186_884 = (translate_expr env e1)
in (let _186_883 = (translate_expr env e2)
in ((_186_884), (_186_883))))
in EBufSub (_186_885))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_881; FStar_Extraction_ML_Syntax.loc = _86_879}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _186_889 = (let _186_888 = (translate_expr env e1)
in (let _186_887 = (translate_expr env e2)
in (let _186_886 = (translate_expr env e3)
in ((_186_888), (_186_887), (_186_886)))))
in EBufWrite (_186_889))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_894; FStar_Extraction_ML_Syntax.loc = _86_892}, (_86_899)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_906; FStar_Extraction_ML_Syntax.loc = _86_904}, (_86_911)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_918; FStar_Extraction_ML_Syntax.loc = _86_916}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _186_895 = (let _186_894 = (translate_expr env e1)
in (let _186_893 = (translate_expr env e2)
in (let _186_892 = (translate_expr env e3)
in (let _186_891 = (translate_expr env e4)
in (let _186_890 = (translate_expr env e5)
in ((_186_894), (_186_893), (_186_892), (_186_891), (_186_890)))))))
in EBufBlit (_186_895))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_933; FStar_Extraction_ML_Syntax.loc = _86_931}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.fill") -> begin
(let _186_899 = (let _186_898 = (translate_expr env e1)
in (let _186_897 = (translate_expr env e2)
in (let _186_896 = (translate_expr env e3)
in ((_186_898), (_186_897), (_186_896)))))
in EBufFill (_186_899))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_946; FStar_Extraction_ML_Syntax.loc = _86_944}, (_86_951)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _86_958; FStar_Extraction_ML_Syntax.loc = _86_956}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
(let _186_901 = (let _186_900 = (translate_expr env e)
in ((_186_900), (TAny)))
in ECast (_186_901))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _86_969; FStar_Extraction_ML_Syntax.loc = _86_967}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _186_903 = (FStar_Util.must (mk_width m))
in (let _186_902 = (FStar_Util.must (mk_op op))
in (mk_op_app env _186_903 _186_902 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _86_983; FStar_Extraction_ML_Syntax.loc = _86_981}, args) when (is_bool_op op) -> begin
(let _186_904 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _186_904 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _186_906 = (let _186_905 = (FStar_Util.must (mk_width m))
in ((_186_905), (c)))
in EConstant (_186_906))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _86_1042; FStar_Extraction_ML_Syntax.loc = _86_1040}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in if ((FStar_Util.ends_with c "uint64") && is_known_type) then begin
(let _186_908 = (let _186_907 = (translate_expr env arg)
in ((_186_907), (TInt (UInt64))))
in ECast (_186_908))
end else begin
if ((FStar_Util.ends_with c "uint32") && is_known_type) then begin
(let _186_910 = (let _186_909 = (translate_expr env arg)
in ((_186_909), (TInt (UInt32))))
in ECast (_186_910))
end else begin
if ((FStar_Util.ends_with c "uint16") && is_known_type) then begin
(let _186_912 = (let _186_911 = (translate_expr env arg)
in ((_186_911), (TInt (UInt16))))
in ECast (_186_912))
end else begin
if ((FStar_Util.ends_with c "uint8") && is_known_type) then begin
(let _186_914 = (let _186_913 = (translate_expr env arg)
in ((_186_913), (TInt (UInt8))))
in ECast (_186_914))
end else begin
if ((FStar_Util.ends_with c "int64") && is_known_type) then begin
(let _186_916 = (let _186_915 = (translate_expr env arg)
in ((_186_915), (TInt (Int64))))
in ECast (_186_916))
end else begin
if ((FStar_Util.ends_with c "int32") && is_known_type) then begin
(let _186_918 = (let _186_917 = (translate_expr env arg)
in ((_186_917), (TInt (Int32))))
in ECast (_186_918))
end else begin
if ((FStar_Util.ends_with c "int16") && is_known_type) then begin
(let _186_920 = (let _186_919 = (translate_expr env arg)
in ((_186_919), (TInt (Int16))))
in ECast (_186_920))
end else begin
if ((FStar_Util.ends_with c "int8") && is_known_type) then begin
(let _186_922 = (let _186_921 = (translate_expr env arg)
in ((_186_921), (TInt (Int8))))
in ECast (_186_922))
end else begin
(let _186_925 = (let _186_924 = (let _186_923 = (translate_expr env arg)
in (_186_923)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (_186_924)))
in EApp (_186_925))
end
end
end
end
end
end
end
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _86_1059; FStar_Extraction_ML_Syntax.loc = _86_1057}, args) -> begin
(let _186_927 = (let _186_926 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_186_926)))
in EApp (_186_927))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _186_930 = (let _186_929 = (translate_expr env e)
in (let _186_928 = (translate_type env t_to)
in ((_186_929), (_186_928))))
in ECast (_186_930))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_86_1074, fields) -> begin
(let _186_935 = (let _186_934 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _186_933 = (FStar_List.map (fun _86_1080 -> (match (_86_1080) with
| (field, expr) -> begin
(let _186_932 = (translate_expr env expr)
in ((field), (_186_932)))
end)) fields)
in ((_186_934), (_186_933))))
in EFlat (_186_935))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _186_938 = (let _186_937 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _186_936 = (translate_expr env e)
in ((_186_937), (_186_936), ((Prims.snd path)))))
in EField (_186_938))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_86_1086) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _86_1090) -> begin
(let _186_940 = (let _186_939 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _186_939))
in (failwith _186_940))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _186_941 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_186_941))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let _186_942 = (FStar_List.map (translate_expr env) es)
in ETuple (_186_942))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((_86_1098, cons), es) -> begin
(let _186_945 = (let _186_944 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _186_943 = (FStar_List.map (translate_expr env) es)
in ((_186_944), (cons), (_186_943))))
in ECons (_186_945))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_86_1105) -> begin
(failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(let _186_949 = (let _186_948 = (translate_expr env e1)
in (let _186_947 = (translate_expr env e2)
in (let _186_946 = (match (e3) with
| None -> begin
EUnit
end
| Some (e3) -> begin
(translate_expr env e3)
end)
in ((_186_948), (_186_947), (_186_946)))))
in EIfThenElse (_186_949))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_86_1116) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_86_1119) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_86_1122) -> begin
(failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
if ((FStar_List.length ts) > (Prims.parse_int "0")) then begin
(let _186_953 = (let _186_952 = (FStar_List.map (translate_type env) ts)
in ((lid), (_186_952)))
in TApp (_186_953))
end else begin
TQualified (lid)
end
end
| _86_1131 -> begin
(failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _86_1138 -> (match (_86_1138) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _86_1141 = (translate_pat env pat)
in (match (_86_1141) with
| (env, pat) -> begin
(let _186_958 = (translate_expr env expr)
in ((pat), (_186_958)))
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, _86_1151) -> begin
(

let env = (extend env name false)
in ((env), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env = (extend env "_" false)
in ((env), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((_86_1158, cons), ps) -> begin
(

let _86_1173 = (FStar_List.fold_left (fun _86_1166 p -> (match (_86_1166) with
| (env, acc) -> begin
(

let _86_1170 = (translate_pat env p)
in (match (_86_1170) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_86_1173) with
| (env, ps) -> begin
((env), (PCons (((cons), ((FStar_List.rev ps))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (_86_1175, ps) -> begin
(

let _86_1190 = (FStar_List.fold_left (fun _86_1181 _86_1184 -> (match (((_86_1181), (_86_1184))) with
| ((env, acc), (field, p)) -> begin
(

let _86_1187 = (translate_pat env p)
in (match (_86_1187) with
| (env, p) -> begin
((env), ((((field), (p)))::acc))
end))
end)) ((env), ([])) ps)
in (match (_86_1190) with
| (env, ps) -> begin
((env), (PRecord ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let _86_1202 = (FStar_List.fold_left (fun _86_1195 p -> (match (_86_1195) with
| (env, acc) -> begin
(

let _86_1199 = (translate_pat env p)
in (match (_86_1199) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_86_1202) with
| (env, ps) -> begin
((env), (PTuple ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (_86_1204) -> begin
(failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_86_1207) -> begin
(failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_86_1215)) -> begin
(failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_86_1220) -> begin
(failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_86_1223) -> begin
(failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_86_1226) -> begin
(failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_86_1229) -> begin
(failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_86_1232, None) -> begin
(failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _186_973 = (let _186_972 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_186_972)))
in EApp (_186_973)))




