
open Prims

type decl =
| DGlobal of (flag Prims.list * lident * typ * expr)
| DFunction of (flag Prims.list * typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * Prims.int * typ)
| DTypeFlat of (lident * (ident * (typ * Prims.bool)) Prims.list)
| DExternal of (lident * typ) 
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


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_81_14) -> begin
_81_14
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_81_17) -> begin
_81_17
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_81_20) -> begin
_81_20
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_81_23) -> begin
_81_23
end))


let ___DExternal____0 = (fun projectee -> (match (projectee) with
| DExternal (_81_26) -> begin
_81_26
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_81_29) -> begin
_81_29
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_81_32) -> begin
_81_32
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_81_35) -> begin
_81_35
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_81_38) -> begin
_81_38
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_81_41) -> begin
_81_41
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_81_44) -> begin
_81_44
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_81_47) -> begin
_81_47
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_81_50) -> begin
_81_50
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_81_53) -> begin
_81_53
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_81_56) -> begin
_81_56
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_81_59) -> begin
_81_59
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_81_62) -> begin
_81_62
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_81_65) -> begin
_81_65
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_81_68) -> begin
_81_68
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_81_71) -> begin
_81_71
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_81_74) -> begin
_81_74
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_81_77) -> begin
_81_77
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_81_80) -> begin
_81_80
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_81_83) -> begin
_81_83
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_81_86) -> begin
_81_86
end))


let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_81_89) -> begin
_81_89
end))


let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_81_92) -> begin
_81_92
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_81_95) -> begin
_81_95
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_81_98) -> begin
_81_98
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_81_102) -> begin
_81_102
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_81_105) -> begin
_81_105
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_81_108) -> begin
_81_108
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_81_111) -> begin
_81_111
end))


let ___TBound____0 = (fun projectee -> (match (projectee) with
| TBound (_81_114) -> begin
_81_114
end))


let ___TApp____0 = (fun projectee -> (match (projectee) with
| TApp (_81_117) -> begin
_81_117
end))


type version =
Prims.int


let current_version : version = (Prims.parse_int "15")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _81_123 -> (match (_81_123) with
| (x, _81_120, _81_122) -> begin
x
end))


let snd3 = (fun _81_129 -> (match (_81_129) with
| (_81_125, x, _81_128) -> begin
x
end))


let thd3 = (fun _81_135 -> (match (_81_135) with
| (_81_131, _81_133, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun _81_1 -> (match (_81_1) with
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
| _81_146 -> begin
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun _81_2 -> (match (_81_2) with
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
| _81_154 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun _81_3 -> (match (_81_3) with
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
| _81_197 -> begin
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

let _81_211 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = _81_211.names_t; module_name = _81_211.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let _81_215 = env
in {names = _81_215.names; names_t = (x)::env.names_t; module_name = _81_215.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _175_601 = (find_name env x)
in _175_601.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _81_231 -> begin
(let _175_609 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _175_609))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| _81_241 -> begin
(let _175_617 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _175_617))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _81_254 -> (match (_81_254) with
| ((name, _81_250), _81_253) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _81_256 -> (match (_81_256) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _81_265 = m
in (match (_81_265) with
| ((prefix, final), _81_262, _81_264) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _81_275 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _175_652 = (translate_module m)
in Some (_175_652)))
end)
with
| e -> begin
(

let _81_271 = (let _175_654 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _175_654))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _81_281 -> (match (_81_281) with
| (module_name, modul, _81_280) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _81_288 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun _81_4 -> (match (_81_4) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| _81_354 -> begin
false
end)) flags)
in (

let flags = if (FStar_Util.for_some (fun _81_5 -> (match (_81_5) with
| FStar_Extraction_ML_Syntax.Private -> begin
true
end
| _81_359 -> begin
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

let rec find_return_type = (fun _81_6 -> (match (_81_6) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_81_365, _81_367, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _175_662 = (find_return_type t0)
in (translate_type env _175_662))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in if assumed then begin
(let _175_665 = (let _175_664 = (let _175_663 = (translate_type env t0)
in ((name), (_175_663)))
in DExternal (_175_664))
in Some (_175_665))
end else begin
try
(match (()) with
| () -> begin
(

let body = (translate_expr env body)
in Some (DFunction (((flags), (t), (name), (binders), (body)))))
end)
with
| e -> begin
(

let _81_380 = (let _175_668 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) _175_668))
in Some (DFunction (((flags), (t), (name), (binders), (EAbort)))))
end
end))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _81_398); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _81_391; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _81_388})::[]) -> begin
(

let flags = if (FStar_Util.for_some (fun _81_7 -> (match (_81_7) with
| FStar_Extraction_ML_Syntax.Private -> begin
true
end
| _81_407 -> begin
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

let _81_415 = (let _175_672 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) _175_672))
in Some (DGlobal (((flags), (name), (t), (EAny)))))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_81_421, _81_423, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _81_435); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _81_431; FStar_Extraction_ML_Syntax.mllb_def = _81_429; FStar_Extraction_ML_Syntax.print_typ = _81_427})::_81_425) -> begin
(

let _81_441 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _81_448 = (match (ts) with
| Some (idents, t) -> begin
(let _175_675 = (let _175_673 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _175_673))
in (let _175_674 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _175_675 _175_674)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_81_451) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_81_454) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, params, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _81_470 -> (match (_81_470) with
| (name, _81_469) -> begin
(extend_t env name)
end)) env params)
in if assumed then begin
None
end else begin
(let _175_680 = (let _175_679 = (let _175_678 = (translate_type env t)
in ((name), ((FStar_List.length params)), (_175_678)))
in DTypeAlias (_175_679))
in Some (_175_680))
end))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_81_473, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _175_686 = (let _175_685 = (let _175_684 = (FStar_List.map (fun _81_485 -> (match (_81_485) with
| (f, t) -> begin
(let _175_683 = (let _175_682 = (translate_type env t)
in ((_175_682), (false)))
in ((f), (_175_683)))
end)) fields)
in ((name), (_175_684)))
in DTypeFlat (_175_685))
in Some (_175_686)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_81_489, name, _81_492, _81_494))::_81_487) -> begin
(

let _81_498 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _81_502 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_81_505) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_81_508) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, _81_517) -> begin
(let _175_689 = (find_t env name)
in TBound (_175_689))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _81_522, t2) -> begin
(let _175_692 = (let _175_691 = (translate_type env t1)
in (let _175_690 = (translate_type env t2)
in ((_175_691), (_175_690))))
in TArrow (_175_692))
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
(let _175_693 = (translate_type env arg)
in TBuf (_175_693))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_81_572)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, type_name)) -> begin
(let _175_695 = (let _175_694 = (FStar_List.map (translate_type env) args)
in ((((path), (type_name))), (_175_694)))
in TApp (_175_695))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_81_590) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _81_600 -> (match (_81_600) with
| ((name, _81_597), typ) -> begin
(let _175_700 = (translate_type env typ)
in {name = name; typ = _175_700; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _81_609) -> begin
(let _175_703 = (find env name)
in EBound (_175_703))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _175_706 = (let _175_705 = (FStar_Util.must (mk_op op))
in (let _175_704 = (FStar_Util.must (mk_width m))
in ((_175_705), (_175_704))))
in EOp (_175_706))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _175_708 = (let _175_707 = (FStar_Util.must (mk_bool_op op))
in ((_175_707), (Bool)))
in EOp (_175_708))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _81_636); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun _81_8 -> (match (_81_8) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| _81_647 -> begin
false
end)) flags)
in (

let _81_671 = if is_mut then begin
(let _175_713 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HyperStack.stackref") -> begin
t
end
| _81_655 -> begin
(let _175_711 = (let _175_710 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _175_710))
in (FStar_All.failwith _175_711))
end)
in (let _175_712 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_81_661, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _81_659; FStar_Extraction_ML_Syntax.loc = _81_657} -> begin
body
end
| _81_668 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_175_713), (_175_712))))
end else begin
((typ), (body))
end
in (match (_81_671) with
| (typ, body) -> begin
(

let binder = (let _175_714 = (translate_type env typ)
in {name = name; typ = _175_714; mut = is_mut})
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
(

let t_scrut = expr.FStar_Extraction_ML_Syntax.mlty
in (let _175_717 = (let _175_716 = (translate_expr env expr)
in (let _175_715 = (translate_branches env t_scrut branches)
in ((_175_716), (_175_715))))
in EMatch (_175_717)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_684; FStar_Extraction_ML_Syntax.loc = _81_682}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _81_694); FStar_Extraction_ML_Syntax.mlty = _81_691; FStar_Extraction_ML_Syntax.loc = _81_689})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _175_718 = (find env v)
in EBound (_175_718))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_704; FStar_Extraction_ML_Syntax.loc = _81_702}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _81_715); FStar_Extraction_ML_Syntax.mlty = _81_712; FStar_Extraction_ML_Syntax.loc = _81_710})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _175_722 = (let _175_721 = (let _175_719 = (find env v)
in EBound (_175_719))
in (let _175_720 = (translate_expr env e)
in ((_175_721), (_175_720))))
in EAssign (_175_722))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_725; FStar_Extraction_ML_Syntax.loc = _81_723}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _175_725 = (let _175_724 = (translate_expr env e1)
in (let _175_723 = (translate_expr env e2)
in ((_175_724), (_175_723))))
in EBufRead (_175_725))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_737; FStar_Extraction_ML_Syntax.loc = _81_735}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _175_728 = (let _175_727 = (translate_expr env e1)
in (let _175_726 = (translate_expr env e2)
in ((_175_727), (_175_726))))
in EBufCreate (_175_728))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_749; FStar_Extraction_ML_Syntax.loc = _81_747}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _81_777 -> begin
(FStar_All.failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (let _175_735 = (let _175_734 = (list_elements e2)
in (FStar_List.map (translate_expr env) _175_734))
in EBufCreateL (_175_735))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_782; FStar_Extraction_ML_Syntax.loc = _81_780}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _175_738 = (let _175_737 = (translate_expr env e1)
in (let _175_736 = (translate_expr env e2)
in ((_175_737), (_175_736))))
in EBufSub (_175_738))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_795; FStar_Extraction_ML_Syntax.loc = _81_793}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _175_741 = (let _175_740 = (translate_expr env e1)
in (let _175_739 = (translate_expr env e2)
in ((_175_740), (_175_739))))
in EBufSub (_175_741))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_807; FStar_Extraction_ML_Syntax.loc = _81_805}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _175_745 = (let _175_744 = (translate_expr env e1)
in (let _175_743 = (translate_expr env e2)
in (let _175_742 = (translate_expr env e3)
in ((_175_744), (_175_743), (_175_742)))))
in EBufWrite (_175_745))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_820; FStar_Extraction_ML_Syntax.loc = _81_818}, (_81_825)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_832; FStar_Extraction_ML_Syntax.loc = _81_830}, (_81_837)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_844; FStar_Extraction_ML_Syntax.loc = _81_842}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _175_751 = (let _175_750 = (translate_expr env e1)
in (let _175_749 = (translate_expr env e2)
in (let _175_748 = (translate_expr env e3)
in (let _175_747 = (translate_expr env e4)
in (let _175_746 = (translate_expr env e5)
in ((_175_750), (_175_749), (_175_748), (_175_747), (_175_746)))))))
in EBufBlit (_175_751))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_859; FStar_Extraction_ML_Syntax.loc = _81_857}, (_81_864)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_871; FStar_Extraction_ML_Syntax.loc = _81_869}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
(let _175_753 = (let _175_752 = (translate_expr env e)
in ((_175_752), (TAny)))
in ECast (_175_753))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _81_882; FStar_Extraction_ML_Syntax.loc = _81_880}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _175_755 = (FStar_Util.must (mk_width m))
in (let _175_754 = (FStar_Util.must (mk_op op))
in (mk_op_app env _175_755 _175_754 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _81_896; FStar_Extraction_ML_Syntax.loc = _81_894}, args) when (is_bool_op op) -> begin
(let _175_756 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _175_756 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _175_758 = (let _175_757 = (FStar_Util.must (mk_width m))
in ((_175_757), (c)))
in EConstant (_175_758))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _81_955; FStar_Extraction_ML_Syntax.loc = _81_953}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in if ((FStar_Util.ends_with c "uint64") && is_known_type) then begin
(let _175_760 = (let _175_759 = (translate_expr env arg)
in ((_175_759), (TInt (UInt64))))
in ECast (_175_760))
end else begin
if ((FStar_Util.ends_with c "uint32") && is_known_type) then begin
(let _175_762 = (let _175_761 = (translate_expr env arg)
in ((_175_761), (TInt (UInt32))))
in ECast (_175_762))
end else begin
if ((FStar_Util.ends_with c "uint16") && is_known_type) then begin
(let _175_764 = (let _175_763 = (translate_expr env arg)
in ((_175_763), (TInt (UInt16))))
in ECast (_175_764))
end else begin
if ((FStar_Util.ends_with c "uint8") && is_known_type) then begin
(let _175_766 = (let _175_765 = (translate_expr env arg)
in ((_175_765), (TInt (UInt8))))
in ECast (_175_766))
end else begin
if ((FStar_Util.ends_with c "int64") && is_known_type) then begin
(let _175_768 = (let _175_767 = (translate_expr env arg)
in ((_175_767), (TInt (Int64))))
in ECast (_175_768))
end else begin
if ((FStar_Util.ends_with c "int32") && is_known_type) then begin
(let _175_770 = (let _175_769 = (translate_expr env arg)
in ((_175_769), (TInt (Int32))))
in ECast (_175_770))
end else begin
if ((FStar_Util.ends_with c "int16") && is_known_type) then begin
(let _175_772 = (let _175_771 = (translate_expr env arg)
in ((_175_771), (TInt (Int16))))
in ECast (_175_772))
end else begin
if ((FStar_Util.ends_with c "int8") && is_known_type) then begin
(let _175_774 = (let _175_773 = (translate_expr env arg)
in ((_175_773), (TInt (Int8))))
in ECast (_175_774))
end else begin
(let _175_777 = (let _175_776 = (let _175_775 = (translate_expr env arg)
in (_175_775)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (_175_776)))
in EApp (_175_777))
end
end
end
end
end
end
end
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _81_972; FStar_Extraction_ML_Syntax.loc = _81_970}, args) -> begin
(let _175_779 = (let _175_778 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_175_778)))
in EApp (_175_779))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _175_782 = (let _175_781 = (translate_expr env e)
in (let _175_780 = (translate_type env t_to)
in ((_175_781), (_175_780))))
in ECast (_175_782))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_81_987, fields) -> begin
(let _175_787 = (let _175_786 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _175_785 = (FStar_List.map (fun _81_993 -> (match (_81_993) with
| (field, expr) -> begin
(let _175_784 = (translate_expr env expr)
in ((field), (_175_784)))
end)) fields)
in ((_175_786), (_175_785))))
in EFlat (_175_787))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _175_790 = (let _175_789 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _175_788 = (translate_expr env e)
in ((_175_789), (_175_788), ((Prims.snd path)))))
in EField (_175_790))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_81_999) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _81_1003) -> begin
(let _175_792 = (let _175_791 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _175_791))
in (FStar_All.failwith _175_792))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_81_1007) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_81_1010) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _175_793 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_175_793))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_81_1015) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_81_1018) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_81_1021) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_81_1024) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_81_1027) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : FStar_Extraction_ML_Syntax.mlty  ->  lident = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], lid) -> begin
lid
end
| _81_1035 -> begin
(FStar_All.failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t_scrut branches -> (FStar_List.map (translate_branch env t_scrut) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t_scrut _81_1044 -> (match (_81_1044) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _81_1047 = (translate_pat env t_scrut pat)
in (match (_81_1047) with
| (env, pat) -> begin
(let _175_801 = (translate_expr env expr)
in ((pat), (_175_801)))
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, _81_1058) -> begin
(

let env = (extend env name false)
in (let _175_807 = (let _175_806 = (let _175_805 = (translate_type env t)
in {name = name; typ = _175_805; mut = false})
in PVar (_175_806))
in ((env), (_175_807))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_81_1064) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_81_1067) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_81_1070) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_81_1073) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_81_1076) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_81_1084)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_81_1089) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_81_1092) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_81_1095) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_81_1098) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_81_1101, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _175_814 = (let _175_813 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_175_813)))
in EApp (_175_814)))




