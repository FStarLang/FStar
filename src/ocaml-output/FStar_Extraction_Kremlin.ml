
open Prims

type decl =
| DFunction of (typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * Prims.int * typ)
| DGlobal of (lident * typ * expr)
| DTypeFlat of (lident * (ident * (typ * Prims.bool)) Prims.list)
| DExternal of (lident * typ) 
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


let is_DGlobal = (fun _discr_ -> (match (_discr_) with
| DGlobal (_) -> begin
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


let is_Mult = (fun _discr_ -> (match (_discr_) with
| Mult (_) -> begin
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


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_84_10) -> begin
_84_10
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_84_13) -> begin
_84_13
end))


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_84_16) -> begin
_84_16
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_84_19) -> begin
_84_19
end))


let ___DExternal____0 = (fun projectee -> (match (projectee) with
| DExternal (_84_22) -> begin
_84_22
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_84_25) -> begin
_84_25
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_84_28) -> begin
_84_28
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_84_31) -> begin
_84_31
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_84_34) -> begin
_84_34
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_84_37) -> begin
_84_37
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_84_40) -> begin
_84_40
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_84_43) -> begin
_84_43
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_84_46) -> begin
_84_46
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_84_49) -> begin
_84_49
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_84_52) -> begin
_84_52
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_84_55) -> begin
_84_55
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_84_58) -> begin
_84_58
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_84_61) -> begin
_84_61
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_84_64) -> begin
_84_64
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_84_67) -> begin
_84_67
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_84_70) -> begin
_84_70
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_84_73) -> begin
_84_73
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_84_76) -> begin
_84_76
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_84_79) -> begin
_84_79
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_84_82) -> begin
_84_82
end))


let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_84_85) -> begin
_84_85
end))


let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_84_88) -> begin
_84_88
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_84_91) -> begin
_84_91
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_84_94) -> begin
_84_94
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_84_98) -> begin
_84_98
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_84_101) -> begin
_84_101
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_84_104) -> begin
_84_104
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_84_107) -> begin
_84_107
end))


let ___TBound____0 = (fun projectee -> (match (projectee) with
| TBound (_84_110) -> begin
_84_110
end))


let ___TApp____0 = (fun projectee -> (match (projectee) with
| TApp (_84_113) -> begin
_84_113
end))


type version =
Prims.int


let current_version : version = (Prims.parse_int "13")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _84_119 -> (match (_84_119) with
| (x, _84_116, _84_118) -> begin
x
end))


let snd3 = (fun _84_125 -> (match (_84_125) with
| (_84_121, x, _84_124) -> begin
x
end))


let thd3 = (fun _84_131 -> (match (_84_131) with
| (_84_127, _84_129, x) -> begin
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
| _84_142 -> begin
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
| _84_150 -> begin
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
| ("op_Greater_Equals_Hat") | ("gte") -> begin
Some (Gte)
end
| ("op_Less_Hat") | ("lt") -> begin
Some (Lt)
end
| ("op_Less_Equals_Hat") | ("lte") -> begin
Some (Lte)
end
| _84_188 -> begin
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

let _84_202 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = _84_202.names_t; module_name = _84_202.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let _84_206 = env
in {names = _84_206.names; names_t = (x)::env.names_t; module_name = _84_206.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _181_597 = (find_name env x)
in _181_597.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _84_222 -> begin
(let _181_605 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _181_605))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| _84_232 -> begin
(let _181_613 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _181_613))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _84_245 -> (match (_84_245) with
| ((name, _84_241), _84_244) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _84_247 -> (match (_84_247) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _84_256 = m
in (match (_84_256) with
| ((prefix, final), _84_253, _84_255) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _84_266 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _181_648 = (translate_module m)
in Some (_181_648)))
end)
with
| e -> begin
(

let _84_262 = (let _181_650 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _181_650))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _84_272 -> (match (_84_272) with
| (module_name, modul, _84_271) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _84_279 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let _84_341 = ()
in try
(match (()) with
| () -> begin
(

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _84_4 -> (match (_84_4) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_84_355, _84_357, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _181_657 = (find_return_type t0)
in (translate_type env _181_657))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in if (flavor = FStar_Extraction_ML_Syntax.Assumed) then begin
(let _181_660 = (let _181_659 = (let _181_658 = (translate_type env t0)
in ((name), (_181_658)))
in DExternal (_181_659))
in Some (_181_660))
end else begin
(

let body = (translate_expr env body)
in Some (DFunction (((t), (name), (binders), (body)))))
end))))))
end)
with
| e -> begin
(

let _84_347 = (let _181_662 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _181_662))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_379); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _84_372; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _84_369})::[]) -> begin
(

let _84_385 = ()
in try
(match (()) with
| () -> begin
(

let t = (translate_type env t)
in (

let expr = (translate_expr env expr)
in (

let name = ((env.module_name), (name))
in Some (DGlobal (((name), (t), (expr)))))))
end)
with
| e -> begin
(

let _84_391 = (let _181_665 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _181_665))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (_84_399, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_411); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _84_407; FStar_Extraction_ML_Syntax.mllb_def = _84_405; FStar_Extraction_ML_Syntax.print_typ = _84_403})::_84_401) -> begin
(

let _84_417 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _84_424 = (match (ts) with
| Some (idents, t) -> begin
(let _181_668 = (let _181_666 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _181_666))
in (let _181_667 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _181_668 _181_667)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_84_427) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_84_430) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, params, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _84_446 -> (match (_84_446) with
| (name, _84_445) -> begin
(extend_t env name)
end)) env params)
in if assumed then begin
None
end else begin
(let _181_673 = (let _181_672 = (let _181_671 = (translate_type env t)
in ((name), ((FStar_List.length params)), (_181_671)))
in DTypeAlias (_181_672))
in Some (_181_673))
end))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_449, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _181_679 = (let _181_678 = (let _181_677 = (FStar_List.map (fun _84_461 -> (match (_84_461) with
| (f, t) -> begin
(let _181_676 = (let _181_675 = (translate_type env t)
in ((_181_675), (false)))
in ((f), (_181_676)))
end)) fields)
in ((name), (_181_677)))
in DTypeFlat (_181_678))
in Some (_181_679)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_465, name, _84_468, _84_470))::_84_463) -> begin
(

let _84_474 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _84_478 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_84_481) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_84_484) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, _84_493) -> begin
(let _181_682 = (find_t env name)
in TBound (_181_682))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _84_498, t2) -> begin
(let _181_685 = (let _181_684 = (translate_type env t1)
in (let _181_683 = (translate_type env t2)
in ((_181_684), (_181_683))))
in TArrow (_181_685))
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
(let _181_686 = (translate_type env arg)
in TBuf (_181_686))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_84_548)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, type_name)) -> begin
(let _181_688 = (let _181_687 = (FStar_List.map (translate_type env) args)
in ((((path), (type_name))), (_181_687)))
in TApp (_181_688))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_84_566) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _84_576 -> (match (_84_576) with
| ((name, _84_573), typ) -> begin
(let _181_693 = (translate_type env typ)
in {name = name; typ = _181_693; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _84_585) -> begin
(let _181_696 = (find env name)
in EBound (_181_696))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _181_699 = (let _181_698 = (FStar_Util.must (mk_op op))
in (let _181_697 = (FStar_Util.must (mk_width m))
in ((_181_698), (_181_697))))
in EOp (_181_699))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _181_701 = (let _181_700 = (FStar_Util.must (mk_bool_op op))
in ((_181_700), (Bool)))
in EOp (_181_701))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_611); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _84_641 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _181_705 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HyperStack.stackref") -> begin
t
end
| _84_625 -> begin
(let _181_703 = (let _181_702 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _181_702))
in (FStar_All.failwith _181_703))
end)
in (let _181_704 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_84_631, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _84_629; FStar_Extraction_ML_Syntax.loc = _84_627} -> begin
body
end
| _84_638 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_181_705), (_181_704))))
end else begin
((typ), (body))
end
in (match (_84_641) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _181_706 = (translate_type env typ)
in {name = name; typ = _181_706; mut = is_mut})
in (

let body = (translate_expr env body)
in (

let env = (extend env name is_mut)
in (

let continuation = (translate_expr env continuation)
in ELet (((binder), (body), (continuation))))))))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(

let t_scrut = expr.FStar_Extraction_ML_Syntax.mlty
in (let _181_709 = (let _181_708 = (translate_expr env expr)
in (let _181_707 = (translate_branches env t_scrut branches)
in ((_181_708), (_181_707))))
in EMatch (_181_709)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_655; FStar_Extraction_ML_Syntax.loc = _84_653}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _84_665); FStar_Extraction_ML_Syntax.mlty = _84_662; FStar_Extraction_ML_Syntax.loc = _84_660})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _181_710 = (find env v)
in EBound (_181_710))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_675; FStar_Extraction_ML_Syntax.loc = _84_673}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _84_686); FStar_Extraction_ML_Syntax.mlty = _84_683; FStar_Extraction_ML_Syntax.loc = _84_681})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _181_714 = (let _181_713 = (let _181_711 = (find env v)
in EBound (_181_711))
in (let _181_712 = (translate_expr env e)
in ((_181_713), (_181_712))))
in EAssign (_181_714))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_696; FStar_Extraction_ML_Syntax.loc = _84_694}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _181_717 = (let _181_716 = (translate_expr env e1)
in (let _181_715 = (translate_expr env e2)
in ((_181_716), (_181_715))))
in EBufRead (_181_717))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_708; FStar_Extraction_ML_Syntax.loc = _84_706}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _181_720 = (let _181_719 = (translate_expr env e1)
in (let _181_718 = (translate_expr env e2)
in ((_181_719), (_181_718))))
in EBufCreate (_181_720))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_720; FStar_Extraction_ML_Syntax.loc = _84_718}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _84_748 -> begin
(FStar_All.failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (let _181_727 = (let _181_726 = (list_elements e2)
in (FStar_List.map (translate_expr env) _181_726))
in EBufCreateL (_181_727))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_753; FStar_Extraction_ML_Syntax.loc = _84_751}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _181_730 = (let _181_729 = (translate_expr env e1)
in (let _181_728 = (translate_expr env e2)
in ((_181_729), (_181_728))))
in EBufSub (_181_730))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_766; FStar_Extraction_ML_Syntax.loc = _84_764}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _181_733 = (let _181_732 = (translate_expr env e1)
in (let _181_731 = (translate_expr env e2)
in ((_181_732), (_181_731))))
in EBufSub (_181_733))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_778; FStar_Extraction_ML_Syntax.loc = _84_776}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _181_737 = (let _181_736 = (translate_expr env e1)
in (let _181_735 = (translate_expr env e2)
in (let _181_734 = (translate_expr env e3)
in ((_181_736), (_181_735), (_181_734)))))
in EBufWrite (_181_737))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_791; FStar_Extraction_ML_Syntax.loc = _84_789}, (_84_796)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_803; FStar_Extraction_ML_Syntax.loc = _84_801}, (_84_808)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_815; FStar_Extraction_ML_Syntax.loc = _84_813}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _181_743 = (let _181_742 = (translate_expr env e1)
in (let _181_741 = (translate_expr env e2)
in (let _181_740 = (translate_expr env e3)
in (let _181_739 = (translate_expr env e4)
in (let _181_738 = (translate_expr env e5)
in ((_181_742), (_181_741), (_181_740), (_181_739), (_181_738)))))))
in EBufBlit (_181_743))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_830; FStar_Extraction_ML_Syntax.loc = _84_828}, (_84_835)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _84_842; FStar_Extraction_ML_Syntax.loc = _84_840}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
(let _181_745 = (let _181_744 = (translate_expr env e)
in ((_181_744), (TAny)))
in ECast (_181_745))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _84_853; FStar_Extraction_ML_Syntax.loc = _84_851}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _181_747 = (FStar_Util.must (mk_width m))
in (let _181_746 = (FStar_Util.must (mk_op op))
in (mk_op_app env _181_747 _181_746 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _84_867; FStar_Extraction_ML_Syntax.loc = _84_865}, args) when (is_bool_op op) -> begin
(let _181_748 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _181_748 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _181_750 = (let _181_749 = (FStar_Util.must (mk_width m))
in ((_181_749), (c)))
in EConstant (_181_750))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _84_926; FStar_Extraction_ML_Syntax.loc = _84_924}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _181_752 = (let _181_751 = (translate_expr env arg)
in ((_181_751), (TInt (UInt64))))
in ECast (_181_752))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _181_754 = (let _181_753 = (translate_expr env arg)
in ((_181_753), (TInt (UInt32))))
in ECast (_181_754))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _181_756 = (let _181_755 = (translate_expr env arg)
in ((_181_755), (TInt (UInt16))))
in ECast (_181_756))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _181_758 = (let _181_757 = (translate_expr env arg)
in ((_181_757), (TInt (UInt8))))
in ECast (_181_758))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _181_760 = (let _181_759 = (translate_expr env arg)
in ((_181_759), (TInt (Int64))))
in ECast (_181_760))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _181_762 = (let _181_761 = (translate_expr env arg)
in ((_181_761), (TInt (Int32))))
in ECast (_181_762))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _181_764 = (let _181_763 = (translate_expr env arg)
in ((_181_763), (TInt (Int16))))
in ECast (_181_764))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _181_766 = (let _181_765 = (translate_expr env arg)
in ((_181_765), (TInt (Int8))))
in ECast (_181_766))
end else begin
(let _181_767 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _181_767))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _84_942; FStar_Extraction_ML_Syntax.loc = _84_940}, args) -> begin
(let _181_769 = (let _181_768 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_181_768)))
in EApp (_181_769))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _181_772 = (let _181_771 = (translate_expr env e)
in (let _181_770 = (translate_type env t_to)
in ((_181_771), (_181_770))))
in ECast (_181_772))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_84_957, fields) -> begin
(let _181_777 = (let _181_776 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _181_775 = (FStar_List.map (fun _84_963 -> (match (_84_963) with
| (field, expr) -> begin
(let _181_774 = (translate_expr env expr)
in ((field), (_181_774)))
end)) fields)
in ((_181_776), (_181_775))))
in EFlat (_181_777))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _181_780 = (let _181_779 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _181_778 = (translate_expr env e)
in ((_181_779), (_181_778), ((Prims.snd path)))))
in EField (_181_780))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_84_969) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _84_973) -> begin
(let _181_782 = (let _181_781 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _181_781))
in (FStar_All.failwith _181_782))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_84_977) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_84_980) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _181_783 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_181_783))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_84_985) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_84_988) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_84_991) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_84_994) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_84_997) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : FStar_Extraction_ML_Syntax.mlty  ->  lident = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], lid) -> begin
lid
end
| _84_1005 -> begin
(FStar_All.failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t_scrut branches -> (FStar_List.map (translate_branch env t_scrut) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t_scrut _84_1014 -> (match (_84_1014) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _84_1017 = (translate_pat env t_scrut pat)
in (match (_84_1017) with
| (env, pat) -> begin
(let _181_791 = (translate_expr env expr)
in ((pat), (_181_791)))
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, _84_1028) -> begin
(

let env = (extend env name false)
in (let _181_797 = (let _181_796 = (let _181_795 = (translate_type env t)
in {name = name; typ = _181_795; mut = false})
in PVar (_181_796))
in ((env), (_181_797))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_84_1034) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_84_1037) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_84_1040) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_84_1043) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_84_1046) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_84_1054)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_84_1059) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_84_1062) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_84_1065) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_84_1068) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_84_1071, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _181_804 = (let _181_803 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_181_803)))
in EApp (_181_804)))




