
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


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))


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
| DGlobal (_83_13) -> begin
_83_13
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_83_16) -> begin
_83_16
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_83_19) -> begin
_83_19
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_83_22) -> begin
_83_22
end))


let ___DExternal____0 = (fun projectee -> (match (projectee) with
| DExternal (_83_25) -> begin
_83_25
end))


let ___DTypeVariant____0 = (fun projectee -> (match (projectee) with
| DTypeVariant (_83_28) -> begin
_83_28
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_83_31) -> begin
_83_31
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_83_34) -> begin
_83_34
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_83_37) -> begin
_83_37
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_83_40) -> begin
_83_40
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_83_43) -> begin
_83_43
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_83_46) -> begin
_83_46
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_83_49) -> begin
_83_49
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_83_52) -> begin
_83_52
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_83_55) -> begin
_83_55
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_83_58) -> begin
_83_58
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_83_61) -> begin
_83_61
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_83_64) -> begin
_83_64
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_83_67) -> begin
_83_67
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_83_70) -> begin
_83_70
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_83_73) -> begin
_83_73
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_83_76) -> begin
_83_76
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_83_79) -> begin
_83_79
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_83_82) -> begin
_83_82
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_83_85) -> begin
_83_85
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_83_88) -> begin
_83_88
end))


let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_83_91) -> begin
_83_91
end))


let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_83_94) -> begin
_83_94
end))


let ___ETuple____0 = (fun projectee -> (match (projectee) with
| ETuple (_83_97) -> begin
_83_97
end))


let ___ECons____0 = (fun projectee -> (match (projectee) with
| ECons (_83_100) -> begin
_83_100
end))


let ___EBufFill____0 = (fun projectee -> (match (projectee) with
| EBufFill (_83_103) -> begin
_83_103
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_83_106) -> begin
_83_106
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_83_109) -> begin
_83_109
end))


let ___PCons____0 = (fun projectee -> (match (projectee) with
| PCons (_83_112) -> begin
_83_112
end))


let ___PTuple____0 = (fun projectee -> (match (projectee) with
| PTuple (_83_115) -> begin
_83_115
end))


let ___PRecord____0 = (fun projectee -> (match (projectee) with
| PRecord (_83_118) -> begin
_83_118
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_83_122) -> begin
_83_122
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_83_125) -> begin
_83_125
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_83_128) -> begin
_83_128
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_83_131) -> begin
_83_131
end))


let ___TBound____0 = (fun projectee -> (match (projectee) with
| TBound (_83_134) -> begin
_83_134
end))


let ___TApp____0 = (fun projectee -> (match (projectee) with
| TApp (_83_137) -> begin
_83_137
end))


let ___TTuple____0 = (fun projectee -> (match (projectee) with
| TTuple (_83_140) -> begin
_83_140
end))


type version =
Prims.int


let current_version : version = (Prims.parse_int "19")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _83_146 -> (match (_83_146) with
| (x, _83_143, _83_145) -> begin
x
end))


let snd3 = (fun _83_152 -> (match (_83_152) with
| (_83_148, x, _83_151) -> begin
x
end))


let thd3 = (fun _83_158 -> (match (_83_158) with
| (_83_154, _83_156, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun _83_1 -> (match (_83_1) with
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
| _83_169 -> begin
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun _83_2 -> (match (_83_2) with
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
| _83_177 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun _83_3 -> (match (_83_3) with
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
| _83_220 -> begin
None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))


type env =
{names : name Prims.list; names_t : Prims.string Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; names_t = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _83_234 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = _83_234.names_t; module_name = _83_234.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let _83_238 = env
in {names = _83_238.names; names_t = (x)::env.names_t; module_name = _83_238.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _180_719 = (find_name env x)
in _180_719.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _83_254 -> begin
(let _180_727 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _180_727))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| _83_264 -> begin
(let _180_735 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _180_735))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _83_277 -> (match (_83_277) with
| ((name, _83_273), _83_276) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _83_279 -> (match (_83_279) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _83_288 = m
in (match (_83_288) with
| ((prefix, final), _83_285, _83_287) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _83_298 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _180_769 = (translate_module m)
in Some (_180_769)))
end)
with
| e -> begin
(

let _83_294 = (let _180_771 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _180_771))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _83_304 -> (match (_83_304) with
| (module_name, modul, _83_303) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _83_311 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_flags : FStar_Extraction_ML_Syntax.c_flag Prims.list  ->  flag Prims.list = (fun flags -> (FStar_List.choose (fun _83_4 -> (match (_83_4) with
| FStar_Extraction_ML_Syntax.Private -> begin
Some (Private)
end
| FStar_Extraction_ML_Syntax.NoExtract -> begin
Some (NoExtract)
end
| _83_318 -> begin
None
end)) flags))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun _83_5 -> (match (_83_5) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| _83_383 -> begin
false
end)) flags)
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_83_389, _83_391, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _180_780 = (find_return_type t0)
in (translate_type env _180_780))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in (

let flags = (translate_flags flags)
in if assumed then begin
(let _180_783 = (let _180_782 = (let _180_781 = (translate_type env t0)
in ((None), (name), (_180_781)))
in DExternal (_180_782))
in Some (_180_783))
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

let _83_405 = (let _180_786 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) _180_786))
in Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort)))))
end
end))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _83_423); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _83_416; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _83_413})::[]) -> begin
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

let _83_436 = (let _180_789 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) _180_789))
in Some (DGlobal (((flags), (name), (t), (EAny)))))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_83_442, _83_444, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _83_456); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _83_452; FStar_Extraction_ML_Syntax.mllb_def = _83_450; FStar_Extraction_ML_Syntax.print_typ = _83_448})::_83_446) -> begin
(

let _83_462 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _83_469 = (match (ts) with
| Some (idents, t) -> begin
(let _180_792 = (let _180_790 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _180_790))
in (let _180_791 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _180_792 _180_791)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_83_472) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_83_475) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _83_492 -> (match (_83_492) with
| (name, _83_491) -> begin
(extend_t env name)
end)) env args)
in if assumed then begin
None
end else begin
(let _180_797 = (let _180_796 = (let _180_795 = (translate_type env t)
in ((name), ((FStar_List.length args)), (_180_795)))
in DTypeAlias (_180_796))
in Some (_180_797))
end))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_83_495, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _83_510 -> (match (_83_510) with
| (name, _83_509) -> begin
(extend_t env name)
end)) env args)
in (let _180_805 = (let _180_804 = (let _180_803 = (FStar_List.map (fun _83_514 -> (match (_83_514) with
| (f, t) -> begin
(let _180_802 = (let _180_801 = (translate_type env t)
in ((_180_801), (false)))
in ((f), (_180_802)))
end)) fields)
in ((name), ((FStar_List.length args)), (_180_803)))
in DTypeFlat (_180_804))
in Some (_180_805))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_83_516, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _83_531 -> (match (_83_531) with
| (name, _83_530) -> begin
(extend_t env name)
end)) env args)
in (let _180_820 = (let _180_819 = (let _180_818 = (FStar_List.mapi (fun i _83_536 -> (match (_83_536) with
| (cons, ts) -> begin
(let _180_817 = (FStar_List.mapi (fun j t -> (let _180_816 = (let _180_813 = (FStar_Util.string_of_int i)
in (let _180_812 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "x%s%s" _180_813 _180_812)))
in (let _180_815 = (let _180_814 = (translate_type env t)
in ((_180_814), (false)))
in ((_180_816), (_180_815))))) ts)
in ((cons), (_180_817)))
end)) branches)
in ((name), ((FStar_List.length args)), (_180_818)))
in DTypeVariant (_180_819))
in Some (_180_820))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_83_542, name, _mangled_name, _83_546, _83_548))::_83_540) -> begin
(

let _83_552 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _83_556 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_83_559) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_83_562) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, _83_571) -> begin
(let _180_823 = (find_t env name)
in TBound (_180_823))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _83_576, t2) -> begin
(let _180_826 = (let _180_825 = (translate_type env t1)
in (let _180_824 = (translate_type env t2)
in ((_180_825), (_180_824))))
in TArrow (_180_826))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t")) when (is_machine_int m) -> begin
(let _180_827 = (FStar_Util.must (mk_width m))
in TInt (_180_827))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (("FStar")::(m)::[], "t\'")) when (is_machine_int m) -> begin
(let _180_828 = (FStar_Util.must (mk_width m))
in TInt (_180_828))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _180_829 = (translate_type env arg)
in TBuf (_180_829))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_83_610)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (("Prims")::[], t)) when (FStar_Util.starts_with t "tuple") -> begin
(let _180_830 = (FStar_List.map (translate_type env) args)
in TTuple (_180_830))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(let _180_832 = (let _180_831 = (FStar_List.map (translate_type env) args)
in ((lid), (_180_831)))
in TApp (_180_832))
end else begin
TQualified (lid)
end
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _180_833 = (FStar_List.map (translate_type env) ts)
in TTuple (_180_833))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _83_642 -> (match (_83_642) with
| ((name, _83_639), typ) -> begin
(let _180_838 = (translate_type env typ)
in {name = name; typ = _180_838; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _83_651) -> begin
(let _180_841 = (find env name)
in EBound (_180_841))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _180_844 = (let _180_843 = (FStar_Util.must (mk_op op))
in (let _180_842 = (FStar_Util.must (mk_width m))
in ((_180_843), (_180_842))))
in EOp (_180_844))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _180_846 = (let _180_845 = (FStar_Util.must (mk_bool_op op))
in ((_180_845), (Bool)))
in EOp (_180_846))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _83_678); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| _83_689 -> begin
false
end)) flags)
in (

let _83_713 = if is_mut then begin
(let _180_851 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.stackref") -> begin
t
end
| _83_697 -> begin
(let _180_849 = (let _180_848 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _180_848))
in (FStar_All.failwith _180_849))
end)
in (let _180_850 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_83_703, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _83_701; FStar_Extraction_ML_Syntax.loc = _83_699} -> begin
body
end
| _83_710 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_180_851), (_180_850))))
end else begin
((typ), (body))
end
in (match (_83_713) with
| (typ, body) -> begin
(

let binder = (let _180_852 = (translate_type env typ)
in {name = name; typ = _180_852; mut = is_mut})
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
(let _180_855 = (let _180_854 = (translate_expr env expr)
in (let _180_853 = (translate_branches env branches)
in ((_180_854), (_180_853))))
in EMatch (_180_855))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_725; FStar_Extraction_ML_Syntax.loc = _83_723}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _83_735); FStar_Extraction_ML_Syntax.mlty = _83_732; FStar_Extraction_ML_Syntax.loc = _83_730})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") && (is_mutable env v)) -> begin
(let _180_856 = (find env v)
in EBound (_180_856))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_745; FStar_Extraction_ML_Syntax.loc = _83_743}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _83_756); FStar_Extraction_ML_Syntax.mlty = _83_753; FStar_Extraction_ML_Syntax.loc = _83_751})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _180_860 = (let _180_859 = (let _180_857 = (find env v)
in EBound (_180_857))
in (let _180_858 = (translate_expr env e)
in ((_180_859), (_180_858))))
in EAssign (_180_860))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_766; FStar_Extraction_ML_Syntax.loc = _83_764}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _180_863 = (let _180_862 = (translate_expr env e1)
in (let _180_861 = (translate_expr env e2)
in ((_180_862), (_180_861))))
in EBufRead (_180_863))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_778; FStar_Extraction_ML_Syntax.loc = _83_776}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _180_866 = (let _180_865 = (translate_expr env e1)
in (let _180_864 = (translate_expr env e2)
in ((Stack), (_180_865), (_180_864))))
in EBufCreate (_180_866))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_790; FStar_Extraction_ML_Syntax.loc = _83_788}, (_e0)::(e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.rcreate") -> begin
(let _180_869 = (let _180_868 = (translate_expr env e1)
in (let _180_867 = (translate_expr env e2)
in ((Eternal), (_180_868), (_180_867))))
in EBufCreate (_180_869))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_803; FStar_Extraction_ML_Syntax.loc = _83_801}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _83_831 -> begin
(FStar_All.failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (let _180_877 = (let _180_876 = (let _180_875 = (list_elements e2)
in (FStar_List.map (translate_expr env) _180_875))
in ((Stack), (_180_876)))
in EBufCreateL (_180_877))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_836; FStar_Extraction_ML_Syntax.loc = _83_834}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _180_880 = (let _180_879 = (translate_expr env e1)
in (let _180_878 = (translate_expr env e2)
in ((_180_879), (_180_878))))
in EBufSub (_180_880))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_849; FStar_Extraction_ML_Syntax.loc = _83_847}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _180_883 = (let _180_882 = (translate_expr env e1)
in (let _180_881 = (translate_expr env e2)
in ((_180_882), (_180_881))))
in EBufSub (_180_883))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_861; FStar_Extraction_ML_Syntax.loc = _83_859}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _180_887 = (let _180_886 = (translate_expr env e1)
in (let _180_885 = (translate_expr env e2)
in (let _180_884 = (translate_expr env e3)
in ((_180_886), (_180_885), (_180_884)))))
in EBufWrite (_180_887))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_874; FStar_Extraction_ML_Syntax.loc = _83_872}, (_83_879)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_886; FStar_Extraction_ML_Syntax.loc = _83_884}, (_83_891)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_898; FStar_Extraction_ML_Syntax.loc = _83_896}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _180_893 = (let _180_892 = (translate_expr env e1)
in (let _180_891 = (translate_expr env e2)
in (let _180_890 = (translate_expr env e3)
in (let _180_889 = (translate_expr env e4)
in (let _180_888 = (translate_expr env e5)
in ((_180_892), (_180_891), (_180_890), (_180_889), (_180_888)))))))
in EBufBlit (_180_893))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_913; FStar_Extraction_ML_Syntax.loc = _83_911}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.fill") -> begin
(let _180_897 = (let _180_896 = (translate_expr env e1)
in (let _180_895 = (translate_expr env e2)
in (let _180_894 = (translate_expr env e3)
in ((_180_896), (_180_895), (_180_894)))))
in EBufFill (_180_897))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_926; FStar_Extraction_ML_Syntax.loc = _83_924}, (_83_931)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _83_938; FStar_Extraction_ML_Syntax.loc = _83_936}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
(let _180_899 = (let _180_898 = (translate_expr env e)
in ((_180_898), (TAny)))
in ECast (_180_899))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _83_949; FStar_Extraction_ML_Syntax.loc = _83_947}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _180_901 = (FStar_Util.must (mk_width m))
in (let _180_900 = (FStar_Util.must (mk_op op))
in (mk_op_app env _180_901 _180_900 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _83_963; FStar_Extraction_ML_Syntax.loc = _83_961}, args) when (is_bool_op op) -> begin
(let _180_902 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _180_902 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _180_904 = (let _180_903 = (FStar_Util.must (mk_width m))
in ((_180_903), (c)))
in EConstant (_180_904))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _83_1022; FStar_Extraction_ML_Syntax.loc = _83_1020}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in if ((FStar_Util.ends_with c "uint64") && is_known_type) then begin
(let _180_906 = (let _180_905 = (translate_expr env arg)
in ((_180_905), (TInt (UInt64))))
in ECast (_180_906))
end else begin
if ((FStar_Util.ends_with c "uint32") && is_known_type) then begin
(let _180_908 = (let _180_907 = (translate_expr env arg)
in ((_180_907), (TInt (UInt32))))
in ECast (_180_908))
end else begin
if ((FStar_Util.ends_with c "uint16") && is_known_type) then begin
(let _180_910 = (let _180_909 = (translate_expr env arg)
in ((_180_909), (TInt (UInt16))))
in ECast (_180_910))
end else begin
if ((FStar_Util.ends_with c "uint8") && is_known_type) then begin
(let _180_912 = (let _180_911 = (translate_expr env arg)
in ((_180_911), (TInt (UInt8))))
in ECast (_180_912))
end else begin
if ((FStar_Util.ends_with c "int64") && is_known_type) then begin
(let _180_914 = (let _180_913 = (translate_expr env arg)
in ((_180_913), (TInt (Int64))))
in ECast (_180_914))
end else begin
if ((FStar_Util.ends_with c "int32") && is_known_type) then begin
(let _180_916 = (let _180_915 = (translate_expr env arg)
in ((_180_915), (TInt (Int32))))
in ECast (_180_916))
end else begin
if ((FStar_Util.ends_with c "int16") && is_known_type) then begin
(let _180_918 = (let _180_917 = (translate_expr env arg)
in ((_180_917), (TInt (Int16))))
in ECast (_180_918))
end else begin
if ((FStar_Util.ends_with c "int8") && is_known_type) then begin
(let _180_920 = (let _180_919 = (translate_expr env arg)
in ((_180_919), (TInt (Int8))))
in ECast (_180_920))
end else begin
(let _180_923 = (let _180_922 = (let _180_921 = (translate_expr env arg)
in (_180_921)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (_180_922)))
in EApp (_180_923))
end
end
end
end
end
end
end
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _83_1039; FStar_Extraction_ML_Syntax.loc = _83_1037}, args) -> begin
(let _180_925 = (let _180_924 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_180_924)))
in EApp (_180_925))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _180_928 = (let _180_927 = (translate_expr env e)
in (let _180_926 = (translate_type env t_to)
in ((_180_927), (_180_926))))
in ECast (_180_928))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_83_1054, fields) -> begin
(let _180_933 = (let _180_932 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _180_931 = (FStar_List.map (fun _83_1060 -> (match (_83_1060) with
| (field, expr) -> begin
(let _180_930 = (translate_expr env expr)
in ((field), (_180_930)))
end)) fields)
in ((_180_932), (_180_931))))
in EFlat (_180_933))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _180_936 = (let _180_935 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _180_934 = (translate_expr env e)
in ((_180_935), (_180_934), ((Prims.snd path)))))
in EField (_180_936))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_83_1066) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _83_1070) -> begin
(let _180_938 = (let _180_937 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _180_937))
in (FStar_All.failwith _180_938))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _180_939 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_180_939))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let _180_940 = (FStar_List.map (translate_expr env) es)
in ETuple (_180_940))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((_83_1078, cons), es) -> begin
(let _180_943 = (let _180_942 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _180_941 = (FStar_List.map (translate_expr env) es)
in ((_180_942), (cons), (_180_941))))
in ECons (_180_943))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_83_1085) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) -> begin
(let _180_947 = (let _180_946 = (translate_expr env e1)
in (let _180_945 = (translate_expr env e2)
in (let _180_944 = (match (e3) with
| None -> begin
EUnit
end
| Some (e3) -> begin
(translate_expr env e3)
end)
in ((_180_946), (_180_945), (_180_944)))))
in EIfThenElse (_180_947))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_83_1096) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_83_1099) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_83_1102) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
if ((FStar_List.length ts) > (Prims.parse_int "0")) then begin
(let _180_951 = (let _180_950 = (FStar_List.map (translate_type env) ts)
in ((lid), (_180_950)))
in TApp (_180_951))
end else begin
TQualified (lid)
end
end
| _83_1111 -> begin
(FStar_All.failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _83_1118 -> (match (_83_1118) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _83_1121 = (translate_pat env pat)
in (match (_83_1121) with
| (env, pat) -> begin
(let _180_956 = (translate_expr env expr)
in ((pat), (_180_956)))
end))
end else begin
(FStar_All.failwith "todo: translate_branch")
end
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  (env * pattern) = (fun env p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
((env), (PUnit))
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (b)) -> begin
((env), (PBool (b)))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name, _83_1131) -> begin
(

let env = (extend env name false)
in ((env), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env = (extend env "_" false)
in ((env), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((_83_1138, cons), ps) -> begin
(

let _83_1153 = (FStar_List.fold_left (fun _83_1146 p -> (match (_83_1146) with
| (env, acc) -> begin
(

let _83_1150 = (translate_pat env p)
in (match (_83_1150) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_83_1153) with
| (env, ps) -> begin
((env), (PCons (((cons), ((FStar_List.rev ps))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (_83_1155, ps) -> begin
(

let _83_1170 = (FStar_List.fold_left (fun _83_1161 _83_1164 -> (match (((_83_1161), (_83_1164))) with
| ((env, acc), (field, p)) -> begin
(

let _83_1167 = (translate_pat env p)
in (match (_83_1167) with
| (env, p) -> begin
((env), ((((field), (p)))::acc))
end))
end)) ((env), ([])) ps)
in (match (_83_1170) with
| (env, ps) -> begin
((env), (PRecord ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let _83_1182 = (FStar_List.fold_left (fun _83_1175 p -> (match (_83_1175) with
| (env, acc) -> begin
(

let _83_1179 = (translate_pat env p)
in (match (_83_1179) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_83_1182) with
| (env, ps) -> begin
((env), (PTuple ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (_83_1184) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_83_1187) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_83_1195)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_83_1200) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_83_1203) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_83_1206) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_83_1209) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_83_1212, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _180_971 = (let _180_970 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_180_970)))
in EApp (_180_971)))




