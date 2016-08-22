
open Prims
# 27 "FStar.Extraction.Kremlin.fst"
type decl =
| DFunction of (typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * typ)
| DGlobal of (lident * typ * expr)
| DTypeFlat of (lident * (ident * typ) Prims.list) 
 and expr =
| EBound of var
| EOpen of binder
| EQualified of lident
| EConstant of constant
| EUnit
| EApp of (expr * expr Prims.list)
| ELet of (binder * expr * expr)
| EIfThenElse of (expr * expr * expr * typ)
| ESequence of expr Prims.list
| EAssign of (expr * expr)
| EBufCreate of (expr * expr)
| EBufRead of (expr * expr)
| EBufWrite of (expr * expr * expr)
| EBufSub of (expr * expr)
| EBufBlit of (expr * expr * expr * expr * expr)
| EMatch of (expr * branches * typ)
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
 and op =
| Add
| AddW
| Sub
| SubW
| Div
| Mult
| Mod
| BOr
| BAnd
| BXor
| BShiftL
| BShiftR
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
{name : ident; typ : typ; mut : Prims.bool; mark : Prims.int FStar_ST.ref; meta : meta Prims.option; atom : Prims.unit FStar_ST.ref} 
 and meta =
| MetaSequence 
 and typ =
| TInt of width
| TBuf of typ
| TUnit
| TQualified of lident
| TBool
| TAny
| TArrow of (typ * typ)
| TZ 
 and program =
decl Prims.list 
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

# 35 "FStar.Extraction.Kremlin.fst"
let is_DFunction = (fun _discr_ -> (match (_discr_) with
| DFunction (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.Kremlin.fst"
let is_DTypeAlias = (fun _discr_ -> (match (_discr_) with
| DTypeAlias (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "FStar.Extraction.Kremlin.fst"
let is_DGlobal = (fun _discr_ -> (match (_discr_) with
| DGlobal (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "FStar.Extraction.Kremlin.fst"
let is_DTypeFlat = (fun _discr_ -> (match (_discr_) with
| DTypeFlat (_) -> begin
true
end
| _ -> begin
false
end))

# 41 "FStar.Extraction.Kremlin.fst"
let is_EBound = (fun _discr_ -> (match (_discr_) with
| EBound (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.Extraction.Kremlin.fst"
let is_EOpen = (fun _discr_ -> (match (_discr_) with
| EOpen (_) -> begin
true
end
| _ -> begin
false
end))

# 43 "FStar.Extraction.Kremlin.fst"
let is_EQualified = (fun _discr_ -> (match (_discr_) with
| EQualified (_) -> begin
true
end
| _ -> begin
false
end))

# 44 "FStar.Extraction.Kremlin.fst"
let is_EConstant = (fun _discr_ -> (match (_discr_) with
| EConstant (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.Extraction.Kremlin.fst"
let is_EUnit = (fun _discr_ -> (match (_discr_) with
| EUnit (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Extraction.Kremlin.fst"
let is_EApp = (fun _discr_ -> (match (_discr_) with
| EApp (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Extraction.Kremlin.fst"
let is_ELet = (fun _discr_ -> (match (_discr_) with
| ELet (_) -> begin
true
end
| _ -> begin
false
end))

# 48 "FStar.Extraction.Kremlin.fst"
let is_EIfThenElse = (fun _discr_ -> (match (_discr_) with
| EIfThenElse (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "FStar.Extraction.Kremlin.fst"
let is_ESequence = (fun _discr_ -> (match (_discr_) with
| ESequence (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.Extraction.Kremlin.fst"
let is_EAssign = (fun _discr_ -> (match (_discr_) with
| EAssign (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.Extraction.Kremlin.fst"
let is_EBufCreate = (fun _discr_ -> (match (_discr_) with
| EBufCreate (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.Extraction.Kremlin.fst"
let is_EBufRead = (fun _discr_ -> (match (_discr_) with
| EBufRead (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.Extraction.Kremlin.fst"
let is_EBufWrite = (fun _discr_ -> (match (_discr_) with
| EBufWrite (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.Extraction.Kremlin.fst"
let is_EBufSub = (fun _discr_ -> (match (_discr_) with
| EBufSub (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.Extraction.Kremlin.fst"
let is_EBufBlit = (fun _discr_ -> (match (_discr_) with
| EBufBlit (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.Extraction.Kremlin.fst"
let is_EMatch = (fun _discr_ -> (match (_discr_) with
| EMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.Extraction.Kremlin.fst"
let is_EOp = (fun _discr_ -> (match (_discr_) with
| EOp (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.Extraction.Kremlin.fst"
let is_ECast = (fun _discr_ -> (match (_discr_) with
| ECast (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.Extraction.Kremlin.fst"
let is_EPushFrame = (fun _discr_ -> (match (_discr_) with
| EPushFrame (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.Extraction.Kremlin.fst"
let is_EPopFrame = (fun _discr_ -> (match (_discr_) with
| EPopFrame (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.Extraction.Kremlin.fst"
let is_EBool = (fun _discr_ -> (match (_discr_) with
| EBool (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.Extraction.Kremlin.fst"
let is_EAny = (fun _discr_ -> (match (_discr_) with
| EAny (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.Extraction.Kremlin.fst"
let is_EAbort = (fun _discr_ -> (match (_discr_) with
| EAbort (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.Extraction.Kremlin.fst"
let is_EReturn = (fun _discr_ -> (match (_discr_) with
| EReturn (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.Extraction.Kremlin.fst"
let is_EFlat = (fun _discr_ -> (match (_discr_) with
| EFlat (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.Extraction.Kremlin.fst"
let is_EField = (fun _discr_ -> (match (_discr_) with
| EField (_) -> begin
true
end
| _ -> begin
false
end))

# 68 "FStar.Extraction.Kremlin.fst"
let is_EWhile = (fun _discr_ -> (match (_discr_) with
| EWhile (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "FStar.Extraction.Kremlin.fst"
let is_EBufCreateL = (fun _discr_ -> (match (_discr_) with
| EBufCreateL (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Extraction.Kremlin.fst"
let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Extraction.Kremlin.fst"
let is_AddW = (fun _discr_ -> (match (_discr_) with
| AddW (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Extraction.Kremlin.fst"
let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Extraction.Kremlin.fst"
let is_SubW = (fun _discr_ -> (match (_discr_) with
| SubW (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Extraction.Kremlin.fst"
let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Extraction.Kremlin.fst"
let is_Mult = (fun _discr_ -> (match (_discr_) with
| Mult (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Extraction.Kremlin.fst"
let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Extraction.Kremlin.fst"
let is_BOr = (fun _discr_ -> (match (_discr_) with
| BOr (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Extraction.Kremlin.fst"
let is_BAnd = (fun _discr_ -> (match (_discr_) with
| BAnd (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Extraction.Kremlin.fst"
let is_BXor = (fun _discr_ -> (match (_discr_) with
| BXor (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Extraction.Kremlin.fst"
let is_BShiftL = (fun _discr_ -> (match (_discr_) with
| BShiftL (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Extraction.Kremlin.fst"
let is_BShiftR = (fun _discr_ -> (match (_discr_) with
| BShiftR (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Extraction.Kremlin.fst"
let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Extraction.Kremlin.fst"
let is_Neq = (fun _discr_ -> (match (_discr_) with
| Neq (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Extraction.Kremlin.fst"
let is_Lt = (fun _discr_ -> (match (_discr_) with
| Lt (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Extraction.Kremlin.fst"
let is_Lte = (fun _discr_ -> (match (_discr_) with
| Lte (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Extraction.Kremlin.fst"
let is_Gt = (fun _discr_ -> (match (_discr_) with
| Gt (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Extraction.Kremlin.fst"
let is_Gte = (fun _discr_ -> (match (_discr_) with
| Gte (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "FStar.Extraction.Kremlin.fst"
let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "FStar.Extraction.Kremlin.fst"
let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "FStar.Extraction.Kremlin.fst"
let is_Xor = (fun _discr_ -> (match (_discr_) with
| Xor (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "FStar.Extraction.Kremlin.fst"
let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.Extraction.Kremlin.fst"
let is_PUnit = (fun _discr_ -> (match (_discr_) with
| PUnit (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.Extraction.Kremlin.fst"
let is_PBool = (fun _discr_ -> (match (_discr_) with
| PBool (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.Extraction.Kremlin.fst"
let is_PVar = (fun _discr_ -> (match (_discr_) with
| PVar (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.Extraction.Kremlin.fst"
let is_UInt8 = (fun _discr_ -> (match (_discr_) with
| UInt8 (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.Extraction.Kremlin.fst"
let is_UInt16 = (fun _discr_ -> (match (_discr_) with
| UInt16 (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.Extraction.Kremlin.fst"
let is_UInt32 = (fun _discr_ -> (match (_discr_) with
| UInt32 (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.Extraction.Kremlin.fst"
let is_UInt64 = (fun _discr_ -> (match (_discr_) with
| UInt64 (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Extraction.Kremlin.fst"
let is_Int8 = (fun _discr_ -> (match (_discr_) with
| Int8 (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Extraction.Kremlin.fst"
let is_Int16 = (fun _discr_ -> (match (_discr_) with
| Int16 (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Extraction.Kremlin.fst"
let is_Int32 = (fun _discr_ -> (match (_discr_) with
| Int32 (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Extraction.Kremlin.fst"
let is_Int64 = (fun _discr_ -> (match (_discr_) with
| Int64 (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "FStar.Extraction.Kremlin.fst"
let is_Bool = (fun _discr_ -> (match (_discr_) with
| Bool (_) -> begin
true
end
| _ -> begin
false
end))

# 92 "FStar.Extraction.Kremlin.fst"
let is_Int = (fun _discr_ -> (match (_discr_) with
| Int (_) -> begin
true
end
| _ -> begin
false
end))

# 92 "FStar.Extraction.Kremlin.fst"
let is_UInt = (fun _discr_ -> (match (_discr_) with
| UInt (_) -> begin
true
end
| _ -> begin
false
end))

# 99 "FStar.Extraction.Kremlin.fst"
let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))

# 109 "FStar.Extraction.Kremlin.fst"
let is_MetaSequence = (fun _discr_ -> (match (_discr_) with
| MetaSequence (_) -> begin
true
end
| _ -> begin
false
end))

# 118 "FStar.Extraction.Kremlin.fst"
let is_TInt = (fun _discr_ -> (match (_discr_) with
| TInt (_) -> begin
true
end
| _ -> begin
false
end))

# 119 "FStar.Extraction.Kremlin.fst"
let is_TBuf = (fun _discr_ -> (match (_discr_) with
| TBuf (_) -> begin
true
end
| _ -> begin
false
end))

# 120 "FStar.Extraction.Kremlin.fst"
let is_TUnit = (fun _discr_ -> (match (_discr_) with
| TUnit (_) -> begin
true
end
| _ -> begin
false
end))

# 121 "FStar.Extraction.Kremlin.fst"
let is_TQualified = (fun _discr_ -> (match (_discr_) with
| TQualified (_) -> begin
true
end
| _ -> begin
false
end))

# 122 "FStar.Extraction.Kremlin.fst"
let is_TBool = (fun _discr_ -> (match (_discr_) with
| TBool (_) -> begin
true
end
| _ -> begin
false
end))

# 123 "FStar.Extraction.Kremlin.fst"
let is_TAny = (fun _discr_ -> (match (_discr_) with
| TAny (_) -> begin
true
end
| _ -> begin
false
end))

# 124 "FStar.Extraction.Kremlin.fst"
let is_TArrow = (fun _discr_ -> (match (_discr_) with
| TArrow (_) -> begin
true
end
| _ -> begin
false
end))

# 125 "FStar.Extraction.Kremlin.fst"
let is_TZ = (fun _discr_ -> (match (_discr_) with
| TZ (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.Kremlin.fst"
let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_80_13) -> begin
_80_13
end))

# 36 "FStar.Extraction.Kremlin.fst"
let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_80_16) -> begin
_80_16
end))

# 37 "FStar.Extraction.Kremlin.fst"
let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_80_19) -> begin
_80_19
end))

# 38 "FStar.Extraction.Kremlin.fst"
let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_80_22) -> begin
_80_22
end))

# 41 "FStar.Extraction.Kremlin.fst"
let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_80_25) -> begin
_80_25
end))

# 42 "FStar.Extraction.Kremlin.fst"
let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_80_28) -> begin
_80_28
end))

# 43 "FStar.Extraction.Kremlin.fst"
let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_80_31) -> begin
_80_31
end))

# 44 "FStar.Extraction.Kremlin.fst"
let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_80_34) -> begin
_80_34
end))

# 46 "FStar.Extraction.Kremlin.fst"
let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_80_37) -> begin
_80_37
end))

# 47 "FStar.Extraction.Kremlin.fst"
let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_80_40) -> begin
_80_40
end))

# 48 "FStar.Extraction.Kremlin.fst"
let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_80_43) -> begin
_80_43
end))

# 49 "FStar.Extraction.Kremlin.fst"
let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_80_46) -> begin
_80_46
end))

# 50 "FStar.Extraction.Kremlin.fst"
let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_80_49) -> begin
_80_49
end))

# 52 "FStar.Extraction.Kremlin.fst"
let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_80_52) -> begin
_80_52
end))

# 53 "FStar.Extraction.Kremlin.fst"
let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_80_55) -> begin
_80_55
end))

# 54 "FStar.Extraction.Kremlin.fst"
let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_80_58) -> begin
_80_58
end))

# 55 "FStar.Extraction.Kremlin.fst"
let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_80_61) -> begin
_80_61
end))

# 56 "FStar.Extraction.Kremlin.fst"
let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_80_64) -> begin
_80_64
end))

# 57 "FStar.Extraction.Kremlin.fst"
let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_80_67) -> begin
_80_67
end))

# 58 "FStar.Extraction.Kremlin.fst"
let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_80_70) -> begin
_80_70
end))

# 59 "FStar.Extraction.Kremlin.fst"
let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_80_73) -> begin
_80_73
end))

# 62 "FStar.Extraction.Kremlin.fst"
let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_80_76) -> begin
_80_76
end))

# 65 "FStar.Extraction.Kremlin.fst"
let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_80_79) -> begin
_80_79
end))

# 66 "FStar.Extraction.Kremlin.fst"
let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_80_82) -> begin
_80_82
end))

# 67 "FStar.Extraction.Kremlin.fst"
let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_80_85) -> begin
_80_85
end))

# 68 "FStar.Extraction.Kremlin.fst"
let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_80_88) -> begin
_80_88
end))

# 69 "FStar.Extraction.Kremlin.fst"
let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_80_91) -> begin
_80_91
end))

# 85 "FStar.Extraction.Kremlin.fst"
let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_80_94) -> begin
_80_94
end))

# 86 "FStar.Extraction.Kremlin.fst"
let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_80_97) -> begin
_80_97
end))

# 118 "FStar.Extraction.Kremlin.fst"
let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_80_101) -> begin
_80_101
end))

# 119 "FStar.Extraction.Kremlin.fst"
let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_80_104) -> begin
_80_104
end))

# 121 "FStar.Extraction.Kremlin.fst"
let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_80_107) -> begin
_80_107
end))

# 124 "FStar.Extraction.Kremlin.fst"
let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_80_110) -> begin
_80_110
end))

# 125 "FStar.Extraction.Kremlin.fst"
type version =
Prims.int

# 129 "FStar.Extraction.Kremlin.fst"
let current_version : version = 10

# 130 "FStar.Extraction.Kremlin.fst"
type file =
(Prims.string * program)

# 132 "FStar.Extraction.Kremlin.fst"
type binary_format =
(version * file Prims.list)

# 133 "FStar.Extraction.Kremlin.fst"
let fst3 = (fun _80_116 -> (match (_80_116) with
| (x, _80_113, _80_115) -> begin
x
end))

# 138 "FStar.Extraction.Kremlin.fst"
let snd3 = (fun _80_122 -> (match (_80_122) with
| (_80_118, x, _80_121) -> begin
x
end))

# 139 "FStar.Extraction.Kremlin.fst"
let thd3 = (fun _80_128 -> (match (_80_128) with
| (_80_124, _80_126, x) -> begin
x
end))

# 140 "FStar.Extraction.Kremlin.fst"
let mk_width : Prims.string  ->  width Prims.option = (fun _80_1 -> (match (_80_1) with
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
| _80_139 -> begin
None
end))

# 151 "FStar.Extraction.Kremlin.fst"
let mk_bool_op : Prims.string  ->  op Prims.option = (fun _80_2 -> (match (_80_2) with
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
| _80_147 -> begin
None
end))

# 165 "FStar.Extraction.Kremlin.fst"
let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))

# 168 "FStar.Extraction.Kremlin.fst"
let mk_op : Prims.string  ->  op Prims.option = (fun _80_3 -> (match (_80_3) with
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
| ("div") | ("op_Slash_Hat") -> begin
Some (Div)
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
| ("op_Greater_Equal_Hat") | ("gte") -> begin
Some (Gte)
end
| ("op_Less_Hat") | ("lt") -> begin
Some (Lt)
end
| ("op_Less_Equal_Hat") | ("lte") -> begin
Some (Lte)
end
| _80_185 -> begin
None
end))

# 206 "FStar.Extraction.Kremlin.fst"
let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> None))

# 209 "FStar.Extraction.Kremlin.fst"
let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))

# 212 "FStar.Extraction.Kremlin.fst"
type env =
{names : name Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}

# 216 "FStar.Extraction.Kremlin.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 221 "FStar.Extraction.Kremlin.fst"
let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))

# 224 "FStar.Extraction.Kremlin.fst"
let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; module_name = module_name})

# 229 "FStar.Extraction.Kremlin.fst"
let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (
# 232 "FStar.Extraction.Kremlin.fst"
let _80_198 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _80_198.module_name}))

# 232 "FStar.Extraction.Kremlin.fst"
let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))

# 239 "FStar.Extraction.Kremlin.fst"
let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _172_572 = (find_name env x)
in _172_572.mut))

# 242 "FStar.Extraction.Kremlin.fst"
let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _80_214 -> begin
(let _172_580 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _172_580))
end)

# 248 "FStar.Extraction.Kremlin.fst"
let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _80_227 -> (match (_80_227) with
| ((name, _80_223), _80_226) -> begin
(extend env name false)
end)) env binders))

# 251 "FStar.Extraction.Kremlin.fst"
let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _80_229 -> (match (_80_229) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (
# 257 "FStar.Extraction.Kremlin.fst"
let m_name = (
# 258 "FStar.Extraction.Kremlin.fst"
let _80_238 = m
in (match (_80_238) with
| ((prefix, final), _80_235, _80_237) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(
# 262 "FStar.Extraction.Kremlin.fst"
let _80_248 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _172_615 = (translate_module m)
in Some (_172_615)))
end)
with
| e -> begin
(
# 266 "FStar.Extraction.Kremlin.fst"
let _80_244 = (let _172_617 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _172_617))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _80_254 -> (match (_80_254) with
| (module_name, modul, _80_253) -> begin
(
# 272 "FStar.Extraction.Kremlin.fst"
let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (
# 273 "FStar.Extraction.Kremlin.fst"
let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _80_261 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_, _, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_, _, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(
# 293 "FStar.Extraction.Kremlin.fst"
let _80_335 = ()
in try
(match (()) with
| () -> begin
(
# 295 "FStar.Extraction.Kremlin.fst"
let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (
# 296 "FStar.Extraction.Kremlin.fst"
let rec find_return_type = (fun _80_4 -> (match (_80_4) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_80_349, _80_351, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (
# 302 "FStar.Extraction.Kremlin.fst"
let t = (let _172_624 = (find_return_type t)
in (translate_type env _172_624))
in (
# 303 "FStar.Extraction.Kremlin.fst"
let binders = (translate_binders env args)
in (
# 304 "FStar.Extraction.Kremlin.fst"
let env = (add_binders env args)
in (
# 305 "FStar.Extraction.Kremlin.fst"
let body = if (flavor = FStar_Extraction_ML_Syntax.Assumed) then begin
EAbort
end else begin
(translate_expr env body)
end
in (
# 311 "FStar.Extraction.Kremlin.fst"
let name = ((env.module_name), (name))
in Some (DFunction (((t), (name), (binders), (body)))))))))))
end)
with
| e -> begin
(
# 314 "FStar.Extraction.Kremlin.fst"
let _80_341 = (let _172_626 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _172_626))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_373); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _80_366; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _80_363})::[]) -> begin
(
# 323 "FStar.Extraction.Kremlin.fst"
let _80_379 = ()
in try
(match (()) with
| () -> begin
(
# 325 "FStar.Extraction.Kremlin.fst"
let t = (translate_type env t)
in (
# 326 "FStar.Extraction.Kremlin.fst"
let expr = (translate_expr env expr)
in (
# 327 "FStar.Extraction.Kremlin.fst"
let name = ((env.module_name), (name))
in Some (DGlobal (((name), (t), (expr)))))))
end)
with
| e -> begin
(
# 330 "FStar.Extraction.Kremlin.fst"
let _80_385 = (let _172_629 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _172_629))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (_80_393, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_405); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_401; FStar_Extraction_ML_Syntax.mllb_def = _80_399; FStar_Extraction_ML_Syntax.print_typ = _80_397})::_80_395) -> begin
(
# 338 "FStar.Extraction.Kremlin.fst"
let _80_411 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (
# 339 "FStar.Extraction.Kremlin.fst"
let _80_418 = (match (ts) with
| Some (idents, t) -> begin
(let _172_632 = (let _172_630 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _172_630))
in (let _172_631 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _172_632 _172_631)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_80_421) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_80_424) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(
# 356 "FStar.Extraction.Kremlin.fst"
let name = ((env.module_name), (name))
in (let _172_635 = (let _172_634 = (let _172_633 = (translate_type env t)
in ((name), (_172_633)))
in DTypeAlias (_172_634))
in Some (_172_635)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(
# 360 "FStar.Extraction.Kremlin.fst"
let name = ((env.module_name), (name))
in (let _172_640 = (let _172_639 = (let _172_638 = (FStar_List.map (fun _80_446 -> (match (_80_446) with
| (f, t) -> begin
(let _172_637 = (translate_type env t)
in ((f), (_172_637)))
end)) fields)
in ((name), (_172_638)))
in DTypeFlat (_172_639))
in Some (_172_640)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, _80_451, _80_453))::_80_448) -> begin
(
# 365 "FStar.Extraction.Kremlin.fst"
let _80_457 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(
# 369 "FStar.Extraction.Kremlin.fst"
let _80_461 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_80_464) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_80_467) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_80_475) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _80_479, t2) -> begin
(let _172_645 = (let _172_644 = (translate_type env t1)
in (let _172_643 = (translate_type env t2)
in ((_172_644), (_172_643))))
in TArrow (_172_645))
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
(let _172_646 = (translate_type env arg)
in TBuf (_172_646))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_80_529)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_80_535, (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_80_542) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _80_552 -> (match (_80_552) with
| ((name, _80_549), typ) -> begin
(let _172_653 = (translate_type env typ)
in (let _172_652 = (FStar_ST.alloc 0)
in (let _172_651 = (FStar_ST.alloc ())
in {name = name; typ = _172_653; mut = false; mark = _172_652; meta = None; atom = _172_651})))
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _80_561) -> begin
(let _172_656 = (find env name)
in EBound (_172_656))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_659 = (let _172_658 = (FStar_Util.must (mk_op op))
in (let _172_657 = (FStar_Util.must (mk_width m))
in ((_172_658), (_172_657))))
in EOp (_172_659))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _172_661 = (let _172_660 = (FStar_Util.must (mk_bool_op op))
in ((_172_660), (Bool)))
in EOp (_172_661))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_587); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(
# 451 "FStar.Extraction.Kremlin.fst"
let _80_617 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _172_663 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.salloc") -> begin
t
end
| _80_601 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _172_662 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_80_607, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _80_605; FStar_Extraction_ML_Syntax.loc = _80_603} -> begin
body
end
| _80_614 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_172_663), (_172_662))))
end else begin
((typ), (body))
end
in (match (_80_617) with
| (typ, body) -> begin
(
# 462 "FStar.Extraction.Kremlin.fst"
let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (
# 463 "FStar.Extraction.Kremlin.fst"
let binder = (let _172_666 = (translate_type env typ)
in (let _172_665 = (FStar_ST.alloc 0)
in (let _172_664 = (FStar_ST.alloc ())
in {name = name; typ = _172_666; mut = is_mut; mark = _172_665; meta = None; atom = _172_664})))
in (
# 464 "FStar.Extraction.Kremlin.fst"
let body = (translate_expr env body)
in (
# 465 "FStar.Extraction.Kremlin.fst"
let env = (extend env name is_mut)
in (
# 466 "FStar.Extraction.Kremlin.fst"
let continuation = (translate_expr env continuation)
in ELet (((binder), (body), (continuation))))))))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(
# 470 "FStar.Extraction.Kremlin.fst"
let t = e.FStar_Extraction_ML_Syntax.mlty
in (let _172_670 = (let _172_669 = (translate_expr env expr)
in (let _172_668 = (translate_branches env t branches)
in (let _172_667 = (translate_type env t)
in ((_172_669), (_172_668), (_172_667)))))
in EMatch (_172_670)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_631; FStar_Extraction_ML_Syntax.loc = _80_629}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _80_641); FStar_Extraction_ML_Syntax.mlty = _80_638; FStar_Extraction_ML_Syntax.loc = _80_636})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _172_671 = (find env v)
in EBound (_172_671))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_651; FStar_Extraction_ML_Syntax.loc = _80_649}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _80_662); FStar_Extraction_ML_Syntax.mlty = _80_659; FStar_Extraction_ML_Syntax.loc = _80_657})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _172_675 = (let _172_674 = (let _172_672 = (find env v)
in EBound (_172_672))
in (let _172_673 = (translate_expr env e)
in ((_172_674), (_172_673))))
in EAssign (_172_675))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_672; FStar_Extraction_ML_Syntax.loc = _80_670}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _172_678 = (let _172_677 = (translate_expr env e1)
in (let _172_676 = (translate_expr env e2)
in ((_172_677), (_172_676))))
in EBufRead (_172_678))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_684; FStar_Extraction_ML_Syntax.loc = _80_682}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _172_681 = (let _172_680 = (translate_expr env e1)
in (let _172_679 = (translate_expr env e2)
in ((_172_680), (_172_679))))
in EBufCreate (_172_681))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_696; FStar_Extraction_ML_Syntax.loc = _80_694}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(
# 485 "FStar.Extraction.Kremlin.fst"
let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _80_724 -> begin
(FStar_All.failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (
# 494 "FStar.Extraction.Kremlin.fst"
let list_elements = (list_elements [])
in (let _172_688 = (let _172_687 = (list_elements e2)
in (FStar_List.map (translate_expr env) _172_687))
in EBufCreateL (_172_688))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_729; FStar_Extraction_ML_Syntax.loc = _80_727}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _172_691 = (let _172_690 = (translate_expr env e1)
in (let _172_689 = (translate_expr env e2)
in ((_172_690), (_172_689))))
in EBufSub (_172_691))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_742; FStar_Extraction_ML_Syntax.loc = _80_740}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _172_694 = (let _172_693 = (translate_expr env e1)
in (let _172_692 = (translate_expr env e2)
in ((_172_693), (_172_692))))
in EBufSub (_172_694))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_754; FStar_Extraction_ML_Syntax.loc = _80_752}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _172_698 = (let _172_697 = (translate_expr env e1)
in (let _172_696 = (translate_expr env e2)
in (let _172_695 = (translate_expr env e3)
in ((_172_697), (_172_696), (_172_695)))))
in EBufWrite (_172_698))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_767; FStar_Extraction_ML_Syntax.loc = _80_765}, (_80_772)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_779; FStar_Extraction_ML_Syntax.loc = _80_777}, (_80_784)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_791; FStar_Extraction_ML_Syntax.loc = _80_789}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _172_704 = (let _172_703 = (translate_expr env e1)
in (let _172_702 = (translate_expr env e2)
in (let _172_701 = (translate_expr env e3)
in (let _172_700 = (translate_expr env e4)
in (let _172_699 = (translate_expr env e5)
in ((_172_703), (_172_702), (_172_701), (_172_700), (_172_699)))))))
in EBufBlit (_172_704))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_806; FStar_Extraction_ML_Syntax.loc = _80_804}, (_80_811)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.get") -> begin
EConstant (((UInt8), ("0")))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _80_818; FStar_Extraction_ML_Syntax.loc = _80_816}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_706 = (FStar_Util.must (mk_width m))
in (let _172_705 = (FStar_Util.must (mk_op op))
in (mk_op_app env _172_706 _172_705 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _80_832; FStar_Extraction_ML_Syntax.loc = _80_830}, args) when (is_bool_op op) -> begin
(let _172_707 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _172_707 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _172_709 = (let _172_708 = (FStar_Util.must (mk_width m))
in ((_172_708), (c)))
in EConstant (_172_709))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _80_891; FStar_Extraction_ML_Syntax.loc = _80_889}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _172_711 = (let _172_710 = (translate_expr env arg)
in ((_172_710), (TInt (UInt64))))
in ECast (_172_711))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _172_713 = (let _172_712 = (translate_expr env arg)
in ((_172_712), (TInt (UInt32))))
in ECast (_172_713))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _172_715 = (let _172_714 = (translate_expr env arg)
in ((_172_714), (TInt (UInt16))))
in ECast (_172_715))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _172_717 = (let _172_716 = (translate_expr env arg)
in ((_172_716), (TInt (UInt8))))
in ECast (_172_717))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _172_719 = (let _172_718 = (translate_expr env arg)
in ((_172_718), (TInt (Int64))))
in ECast (_172_719))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _172_721 = (let _172_720 = (translate_expr env arg)
in ((_172_720), (TInt (Int32))))
in ECast (_172_721))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _172_723 = (let _172_722 = (translate_expr env arg)
in ((_172_722), (TInt (Int16))))
in ECast (_172_723))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _172_725 = (let _172_724 = (translate_expr env arg)
in ((_172_724), (TInt (Int8))))
in ECast (_172_725))
end else begin
(let _172_726 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _172_726))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _80_907; FStar_Extraction_ML_Syntax.loc = _80_905}, args) -> begin
(let _172_728 = (let _172_727 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_172_727)))
in EApp (_172_728))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _172_731 = (let _172_730 = (translate_expr env e)
in (let _172_729 = (translate_type env t_to)
in ((_172_730), (_172_729))))
in ECast (_172_731))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_80_922, fields) -> begin
(let _172_736 = (let _172_735 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _172_734 = (FStar_List.map (fun _80_928 -> (match (_80_928) with
| (field, expr) -> begin
(let _172_733 = (translate_expr env expr)
in ((field), (_172_733)))
end)) fields)
in ((_172_735), (_172_734))))
in EFlat (_172_736))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _172_739 = (let _172_738 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _172_737 = (translate_expr env e)
in ((_172_738), (_172_737), ((Prims.snd path)))))
in EField (_172_739))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_80_934) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _80_938) -> begin
(let _172_741 = (let _172_740 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _172_740))
in (FStar_All.failwith _172_741))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_80_942) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_80_945) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _172_742 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_172_742))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_80_950) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_80_953) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_80_956) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_80_959) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_80_962) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : FStar_Extraction_ML_Syntax.mlty  ->  lident = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], lid) -> begin
lid
end
| _80_970 -> begin
(FStar_All.failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t branches -> (FStar_List.map (translate_branch env t) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t _80_979 -> (match (_80_979) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(
# 593 "FStar.Extraction.Kremlin.fst"
let _80_982 = (translate_pat env t pat)
in (match (_80_982) with
| (env, pat) -> begin
(let _172_750 = (translate_expr env expr)
in ((pat), (_172_750)))
end))
end else begin
(FStar_All.failwith "todo: translate_branch")
end
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  (env * pattern) = (fun env t p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
((env), (PUnit))
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (b)) -> begin
((env), (PBool (b)))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name, _80_993) -> begin
(
# 605 "FStar.Extraction.Kremlin.fst"
let env = (extend env name false)
in (let _172_758 = (let _172_757 = (let _172_756 = (translate_type env t)
in (let _172_755 = (FStar_ST.alloc 0)
in (let _172_754 = (FStar_ST.alloc ())
in {name = name; typ = _172_756; mut = false; mark = _172_755; meta = None; atom = _172_754})))
in PVar (_172_757))
in ((env), (_172_758))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_80_999) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_80_1002) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_80_1005) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_80_1008) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_80_1011) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_80_1019)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_80_1024) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_80_1027) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_80_1030) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_80_1033) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_80_1036, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _172_765 = (let _172_764 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_172_764)))
in EApp (_172_765)))




