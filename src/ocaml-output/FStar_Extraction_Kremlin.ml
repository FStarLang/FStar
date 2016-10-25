
open Prims

type decl =
| DGlobal of (flag Prims.list * lident * typ * expr)
| DFunction of (cc Prims.option * flag Prims.list * typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * Prims.int * typ)
| DTypeFlat of (lident * fields_t)
| DExternal of (cc Prims.option * lident * typ)
| DTypeVariant of (lident * branches_t) 
 and cc =
| StdCall
| CDecl
| FastCall 
 and flag =
| Private 
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
| EBufCreate of (expr * expr)
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
| EFlat of (lident * (ident * expr) Prims.list)
| EField of (lident * expr * ident)
| EWhile of (expr * expr)
| EBufCreateL of expr Prims.list
| ETuple of expr Prims.list
| ECons of (lident * ident * expr Prims.list) 
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
| DGlobal (_84_14) -> begin
_84_14
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_84_17) -> begin
_84_17
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_84_20) -> begin
_84_20
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_84_23) -> begin
_84_23
end))


let ___DExternal____0 = (fun projectee -> (match (projectee) with
| DExternal (_84_26) -> begin
_84_26
end))


let ___DTypeVariant____0 = (fun projectee -> (match (projectee) with
| DTypeVariant (_84_29) -> begin
_84_29
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_84_32) -> begin
_84_32
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_84_35) -> begin
_84_35
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_84_38) -> begin
_84_38
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_84_41) -> begin
_84_41
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_84_44) -> begin
_84_44
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_84_47) -> begin
_84_47
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_84_50) -> begin
_84_50
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_84_53) -> begin
_84_53
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_84_56) -> begin
_84_56
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_84_59) -> begin
_84_59
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_84_62) -> begin
_84_62
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_84_65) -> begin
_84_65
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_84_68) -> begin
_84_68
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_84_71) -> begin
_84_71
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_84_74) -> begin
_84_74
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_84_77) -> begin
_84_77
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_84_80) -> begin
_84_80
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_84_83) -> begin
_84_83
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_84_86) -> begin
_84_86
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_84_89) -> begin
_84_89
end))


let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_84_92) -> begin
_84_92
end))


let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_84_95) -> begin
_84_95
end))


let ___ETuple____0 = (fun projectee -> (match (projectee) with
| ETuple (_84_98) -> begin
_84_98
end))


let ___ECons____0 = (fun projectee -> (match (projectee) with
| ECons (_84_101) -> begin
_84_101
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_84_104) -> begin
_84_104
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_84_107) -> begin
_84_107
end))


let ___PCons____0 = (fun projectee -> (match (projectee) with
| PCons (_84_110) -> begin
_84_110
end))


let ___PTuple____0 = (fun projectee -> (match (projectee) with
| PTuple (_84_113) -> begin
_84_113
end))


let ___PRecord____0 = (fun projectee -> (match (projectee) with
| PRecord (_84_116) -> begin
_84_116
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_84_120) -> begin
_84_120
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_84_123) -> begin
_84_123
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_84_126) -> begin
_84_126
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_84_129) -> begin
_84_129
end))


let ___TBound____0 = (fun projectee -> (match (projectee) with
| TBound (_84_132) -> begin
_84_132
end))


let ___TApp____0 = (fun projectee -> (match (projectee) with
| TApp (_84_135) -> begin
_84_135
end))


let ___TTuple____0 = (fun projectee -> (match (projectee) with
| TTuple (_84_138) -> begin
_84_138
end))


type version =
Prims.int


let current_version : version = (Prims.parse_int "17")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _84_144 -> (match (_84_144) with
| (x, _84_141, _84_143) -> begin
x
end))


let snd3 = (fun _84_150 -> (match (_84_150) with
| (_84_146, x, _84_149) -> begin
x
end))


let thd3 = (fun _84_156 -> (match (_84_156) with
| (_84_152, _84_154, x) -> begin
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
| _84_167 -> begin
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
| _84_175 -> begin
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
| _84_218 -> begin
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

let _84_232 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = _84_232.names_t; module_name = _84_232.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let _84_236 = env
in {names = _84_236.names; names_t = (x)::env.names_t; module_name = _84_236.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _181_702 = (find_name env x)
in _181_702.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _84_252 -> begin
(let _181_710 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _181_710))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| _84_262 -> begin
(let _181_718 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _181_718))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _84_275 -> (match (_84_275) with
| ((name, _84_271), _84_274) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _84_277 -> (match (_84_277) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _84_286 = m
in (match (_84_286) with
| ((prefix, final), _84_283, _84_285) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _84_296 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _181_750 = (translate_module m)
in Some (_181_750)))
end)
with
| e -> begin
(

let _84_292 = (let _181_752 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _181_752))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _84_302 -> (match (_84_302) with
| (module_name, modul, _84_301) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _84_309 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun _84_4 -> (match (_84_4) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| _84_375 -> begin
false
end)) flags)
in (

let flags = if (FStar_Util.for_some (fun _84_5 -> (match (_84_5) with
| FStar_Extraction_ML_Syntax.Private -> begin
true
end
| _84_380 -> begin
false
end)) flags) then begin
(Private)::[]
end else begin
[]
end
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _84_6 -> (match (_84_6) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_84_386, _84_388, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _181_760 = (find_return_type t0)
in (translate_type env _181_760))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in if assumed then begin
(let _181_763 = (let _181_762 = (let _181_761 = (translate_type env t0)
in ((None), (name), (_181_761)))
in DExternal (_181_762))
in Some (_181_763))
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

let _84_401 = (let _181_766 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) _181_766))
in Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort)))))
end
end))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_419); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _84_412; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _84_409})::[]) -> begin
(

let flags = if (FStar_Util.for_some (fun _84_7 -> (match (_84_7) with
| FStar_Extraction_ML_Syntax.Private -> begin
true
end
| _84_428 -> begin
false
end)) flags) then begin
(Private)::[]
end else begin
[]
end
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

let _84_436 = (let _181_770 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) _181_770))
in Some (DGlobal (((flags), (name), (t), (EAny)))))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_84_442, _84_444, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_456); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _84_452; FStar_Extraction_ML_Syntax.mllb_def = _84_450; FStar_Extraction_ML_Syntax.print_typ = _84_448})::_84_446) -> begin
(

let _84_462 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _84_469 = (match (ts) with
| Some (idents, t) -> begin
(let _181_773 = (let _181_771 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _181_771))
in (let _181_772 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _181_773 _181_772)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_84_472) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_84_475) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _84_491 -> (match (_84_491) with
| (name, _84_490) -> begin
(extend_t env name)
end)) env args)
in if assumed then begin
None
end else begin
(let _181_778 = (let _181_777 = (let _181_776 = (translate_type env t)
in ((name), ((FStar_List.length args)), (_181_776)))
in DTypeAlias (_181_777))
in Some (_181_778))
end))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_494, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _181_784 = (let _181_783 = (let _181_782 = (FStar_List.map (fun _84_506 -> (match (_84_506) with
| (f, t) -> begin
(let _181_781 = (let _181_780 = (translate_type env t)
in ((_181_780), (false)))
in ((f), (_181_781)))
end)) fields)
in ((name), (_181_782)))
in DTypeFlat (_181_783))
in Some (_181_784)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_508, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _181_795 = (let _181_794 = (let _181_793 = (FStar_List.map (fun _84_520 -> (match (_84_520) with
| (cons, ts) -> begin
(let _181_792 = (FStar_List.mapi (fun i t -> (let _181_791 = (let _181_788 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "x%s" _181_788))
in (let _181_790 = (let _181_789 = (translate_type env t)
in ((_181_789), (false)))
in ((_181_791), (_181_790))))) ts)
in ((cons), (_181_792)))
end)) branches)
in ((name), (_181_793)))
in DTypeVariant (_181_794))
in Some (_181_795)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_526, name, _84_529, _84_531))::_84_524) -> begin
(

let _84_535 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _84_539 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_84_542) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_84_545) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, _84_554) -> begin
(let _181_798 = (find_t env name)
in TBound (_181_798))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _84_559, t2) -> begin
(let _181_801 = (let _181_800 = (translate_type env t1)
in (let _181_799 = (translate_type env t2)
in ((_181_800), (_181_799))))
in TArrow (_181_801))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt8.t") -> begin
TInt (UInt8)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt16.t") -> begin
TInt (UInt16)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt32.t") -> begin
TInt (UInt32)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt64.t") -> begin
TInt (UInt64)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int8.t") -> begin
TInt (Int8)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int16.t") -> begin
TInt (Int16)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int32.t") -> begin
TInt (Int32)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int64.t") -> begin
TInt (Int64)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _181_802 = (translate_type env arg)
in TBuf (_181_802))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_84_609)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (("Prims")::[], t)) when (FStar_Util.starts_with t "tuple") -> begin
(let _181_803 = (FStar_List.map (translate_type env) args)
in TTuple (_181_803))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, type_name)) -> begin
(let _181_805 = (let _181_804 = (FStar_List.map (translate_type env) args)
in ((((path), (type_name))), (_181_804)))
in TApp (_181_805))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _181_806 = (FStar_List.map (translate_type env) ts)
in TTuple (_181_806))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _84_643 -> (match (_84_643) with
| ((name, _84_640), typ) -> begin
(let _181_811 = (translate_type env typ)
in {name = name; typ = _181_811; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _84_652) -> begin
(let _181_814 = (find env name)
in EBound (_181_814))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _181_817 = (let _181_816 = (FStar_Util.must (mk_op op))
in (let _181_815 = (FStar_Util.must (mk_width m))
in ((_181_816), (_181_815))))
in EOp (_181_817))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _181_819 = (let _181_818 = (FStar_Util.must (mk_bool_op op))
in ((_181_818), (Bool)))
in EOp (_181_819))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_679); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun _84_8 -> (match (_84_8) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| _84_690 -> begin
false
end)) flags)
in (

let _84_714 = if is_mut then begin
(let _181_824 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.stackref") -> begin
t
end
| _84_698 -> begin
(let _181_822 = (let _181_821 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _181_821))
in (FStar_All.failwith _181_822))
end)
in (let _181_823 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_84_704, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _84_702; FStar_Extraction_ML_Syntax.loc = _84_700} -> begin
body
end
| _84_711 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_181_824), (_181_823))))
end else begin
((typ), (body))
end
in (match (_84_714) with
| (typ, body) -> begin
(

let binder = (let _181_825 = (translate_type env typ)
in {name = name; typ = _181_825; mut = is_mut})
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
(let _181_828 = (let _181_827 = (translate_expr env expr)
in (let _181_826 = (translate_branches env branches)
in ((_181_827), (_181_826))))
in EMatch (_181_828))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_726; FStar_Extraction_ML_Syntax.loc = _84_724}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _84_736); FStar_Extraction_ML_Syntax.mlty = _84_733; FStar_Extraction_ML_Syntax.loc = _84_731})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") && (is_mutable env v)) -> begin
(let _181_829 = (find env v)
in EBound (_181_829))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_746; FStar_Extraction_ML_Syntax.loc = _84_744}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _84_757); FStar_Extraction_ML_Syntax.mlty = _84_754; FStar_Extraction_ML_Syntax.loc = _84_752})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _181_833 = (let _181_832 = (let _181_830 = (find env v)
in EBound (_181_830))
in (let _181_831 = (translate_expr env e)
in ((_181_832), (_181_831))))
in EAssign (_181_833))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_767; FStar_Extraction_ML_Syntax.loc = _84_765}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _181_836 = (let _181_835 = (translate_expr env e1)
in (let _181_834 = (translate_expr env e2)
in ((_181_835), (_181_834))))
in EBufRead (_181_836))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_779; FStar_Extraction_ML_Syntax.loc = _84_777}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _181_839 = (let _181_838 = (translate_expr env e1)
in (let _181_837 = (translate_expr env e2)
in ((_181_838), (_181_837))))
in EBufCreate (_181_839))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_791; FStar_Extraction_ML_Syntax.loc = _84_789}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _84_819 -> begin
(FStar_All.failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (let _181_846 = (let _181_845 = (list_elements e2)
in (FStar_List.map (translate_expr env) _181_845))
in EBufCreateL (_181_846))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_824; FStar_Extraction_ML_Syntax.loc = _84_822}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _181_849 = (let _181_848 = (translate_expr env e1)
in (let _181_847 = (translate_expr env e2)
in ((_181_848), (_181_847))))
in EBufSub (_181_849))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_837; FStar_Extraction_ML_Syntax.loc = _84_835}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _181_852 = (let _181_851 = (translate_expr env e1)
in (let _181_850 = (translate_expr env e2)
in ((_181_851), (_181_850))))
in EBufSub (_181_852))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_849; FStar_Extraction_ML_Syntax.loc = _84_847}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _181_856 = (let _181_855 = (translate_expr env e1)
in (let _181_854 = (translate_expr env e2)
in (let _181_853 = (translate_expr env e3)
in ((_181_855), (_181_854), (_181_853)))))
in EBufWrite (_181_856))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_862; FStar_Extraction_ML_Syntax.loc = _84_860}, (_84_867)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_874; FStar_Extraction_ML_Syntax.loc = _84_872}, (_84_879)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_886; FStar_Extraction_ML_Syntax.loc = _84_884}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _181_862 = (let _181_861 = (translate_expr env e1)
in (let _181_860 = (translate_expr env e2)
in (let _181_859 = (translate_expr env e3)
in (let _181_858 = (translate_expr env e4)
in (let _181_857 = (translate_expr env e5)
in ((_181_861), (_181_860), (_181_859), (_181_858), (_181_857)))))))
in EBufBlit (_181_862))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_901; FStar_Extraction_ML_Syntax.loc = _84_899}, (_84_906)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_913; FStar_Extraction_ML_Syntax.loc = _84_911}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
(let _181_864 = (let _181_863 = (translate_expr env e)
in ((_181_863), (TAny)))
in ECast (_181_864))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _84_924; FStar_Extraction_ML_Syntax.loc = _84_922}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _181_866 = (FStar_Util.must (mk_width m))
in (let _181_865 = (FStar_Util.must (mk_op op))
in (mk_op_app env _181_866 _181_865 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _84_938; FStar_Extraction_ML_Syntax.loc = _84_936}, args) when (is_bool_op op) -> begin
(let _181_867 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _181_867 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _181_869 = (let _181_868 = (FStar_Util.must (mk_width m))
in ((_181_868), (c)))
in EConstant (_181_869))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _84_997; FStar_Extraction_ML_Syntax.loc = _84_995}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in if ((FStar_Util.ends_with c "uint64") && is_known_type) then begin
(let _181_871 = (let _181_870 = (translate_expr env arg)
in ((_181_870), (TInt (UInt64))))
in ECast (_181_871))
end else begin
if ((FStar_Util.ends_with c "uint32") && is_known_type) then begin
(let _181_873 = (let _181_872 = (translate_expr env arg)
in ((_181_872), (TInt (UInt32))))
in ECast (_181_873))
end else begin
if ((FStar_Util.ends_with c "uint16") && is_known_type) then begin
(let _181_875 = (let _181_874 = (translate_expr env arg)
in ((_181_874), (TInt (UInt16))))
in ECast (_181_875))
end else begin
if ((FStar_Util.ends_with c "uint8") && is_known_type) then begin
(let _181_877 = (let _181_876 = (translate_expr env arg)
in ((_181_876), (TInt (UInt8))))
in ECast (_181_877))
end else begin
if ((FStar_Util.ends_with c "int64") && is_known_type) then begin
(let _181_879 = (let _181_878 = (translate_expr env arg)
in ((_181_878), (TInt (Int64))))
in ECast (_181_879))
end else begin
if ((FStar_Util.ends_with c "int32") && is_known_type) then begin
(let _181_881 = (let _181_880 = (translate_expr env arg)
in ((_181_880), (TInt (Int32))))
in ECast (_181_881))
end else begin
if ((FStar_Util.ends_with c "int16") && is_known_type) then begin
(let _181_883 = (let _181_882 = (translate_expr env arg)
in ((_181_882), (TInt (Int16))))
in ECast (_181_883))
end else begin
if ((FStar_Util.ends_with c "int8") && is_known_type) then begin
(let _181_885 = (let _181_884 = (translate_expr env arg)
in ((_181_884), (TInt (Int8))))
in ECast (_181_885))
end else begin
(let _181_888 = (let _181_887 = (let _181_886 = (translate_expr env arg)
in (_181_886)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (_181_887)))
in EApp (_181_888))
end
end
end
end
end
end
end
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _84_1014; FStar_Extraction_ML_Syntax.loc = _84_1012}, args) -> begin
(let _181_890 = (let _181_889 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_181_889)))
in EApp (_181_890))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _181_893 = (let _181_892 = (translate_expr env e)
in (let _181_891 = (translate_type env t_to)
in ((_181_892), (_181_891))))
in ECast (_181_893))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_84_1029, fields) -> begin
(let _181_898 = (let _181_897 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _181_896 = (FStar_List.map (fun _84_1035 -> (match (_84_1035) with
| (field, expr) -> begin
(let _181_895 = (translate_expr env expr)
in ((field), (_181_895)))
end)) fields)
in ((_181_897), (_181_896))))
in EFlat (_181_898))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _181_901 = (let _181_900 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _181_899 = (translate_expr env e)
in ((_181_900), (_181_899), ((Prims.snd path)))))
in EField (_181_901))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_84_1041) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _84_1045) -> begin
(let _181_903 = (let _181_902 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _181_902))
in (FStar_All.failwith _181_903))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _181_904 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_181_904))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let _181_905 = (FStar_List.map (translate_expr env) es)
in ETuple (_181_905))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((_84_1053, cons), es) -> begin
(let _181_908 = (let _181_907 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _181_906 = (FStar_List.map (translate_expr env) es)
in ((_181_907), (cons), (_181_906))))
in ECons (_181_908))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_84_1060) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_84_1063) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_84_1066) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_84_1069) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_84_1072) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : FStar_Extraction_ML_Syntax.mlty  ->  lident = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], lid) -> begin
lid
end
| _84_1080 -> begin
(FStar_All.failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _84_1087 -> (match (_84_1087) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _84_1090 = (translate_pat env pat)
in (match (_84_1090) with
| (env, pat) -> begin
(let _181_914 = (translate_expr env expr)
in ((pat), (_181_914)))
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, _84_1100) -> begin
(

let env = (extend env name false)
in ((env), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env = (extend env "_" false)
in ((env), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((_84_1107, cons), ps) -> begin
(

let _84_1122 = (FStar_List.fold_left (fun _84_1115 p -> (match (_84_1115) with
| (env, acc) -> begin
(

let _84_1119 = (translate_pat env p)
in (match (_84_1119) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_84_1122) with
| (env, ps) -> begin
((env), (PCons (((cons), ((FStar_List.rev ps))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (_84_1124, ps) -> begin
(

let _84_1139 = (FStar_List.fold_left (fun _84_1130 _84_1133 -> (match (((_84_1130), (_84_1133))) with
| ((env, acc), (field, p)) -> begin
(

let _84_1136 = (translate_pat env p)
in (match (_84_1136) with
| (env, p) -> begin
((env), ((((field), (p)))::acc))
end))
end)) ((env), ([])) ps)
in (match (_84_1139) with
| (env, ps) -> begin
((env), (PRecord ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let _84_1151 = (FStar_List.fold_left (fun _84_1144 p -> (match (_84_1144) with
| (env, acc) -> begin
(

let _84_1148 = (translate_pat env p)
in (match (_84_1148) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_84_1151) with
| (env, ps) -> begin
((env), (PTuple ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (_84_1153) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_84_1156) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_84_1164)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_84_1169) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_84_1172) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_84_1175) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_84_1178) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_84_1181, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _181_929 = (let _181_928 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_181_928)))
in EApp (_181_929)))




