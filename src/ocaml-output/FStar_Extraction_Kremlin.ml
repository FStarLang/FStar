
open Prims

type decl =
| DFunction of (typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * typ)
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


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_81_10) -> begin
_81_10
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_81_13) -> begin
_81_13
end))


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_81_16) -> begin
_81_16
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_81_19) -> begin
_81_19
end))


let ___DExternal____0 = (fun projectee -> (match (projectee) with
| DExternal (_81_22) -> begin
_81_22
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_81_25) -> begin
_81_25
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_81_28) -> begin
_81_28
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_81_31) -> begin
_81_31
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_81_34) -> begin
_81_34
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_81_37) -> begin
_81_37
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_81_40) -> begin
_81_40
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_81_43) -> begin
_81_43
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_81_46) -> begin
_81_46
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_81_49) -> begin
_81_49
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_81_52) -> begin
_81_52
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_81_55) -> begin
_81_55
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_81_58) -> begin
_81_58
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_81_61) -> begin
_81_61
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_81_64) -> begin
_81_64
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_81_67) -> begin
_81_67
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_81_70) -> begin
_81_70
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_81_73) -> begin
_81_73
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_81_76) -> begin
_81_76
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_81_79) -> begin
_81_79
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_81_82) -> begin
_81_82
end))


let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_81_85) -> begin
_81_85
end))


let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_81_88) -> begin
_81_88
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_81_91) -> begin
_81_91
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_81_94) -> begin
_81_94
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_81_98) -> begin
_81_98
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_81_101) -> begin
_81_101
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_81_104) -> begin
_81_104
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_81_107) -> begin
_81_107
end))


type version =
Prims.int


let current_version : version = (Prims.parse_int "12")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _81_113 -> (match (_81_113) with
| (x, _81_110, _81_112) -> begin
x
end))


let snd3 = (fun _81_119 -> (match (_81_119) with
| (_81_115, x, _81_118) -> begin
x
end))


let thd3 = (fun _81_125 -> (match (_81_125) with
| (_81_121, _81_123, x) -> begin
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
| _81_136 -> begin
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
| _81_144 -> begin
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
| _81_182 -> begin
None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))


type env =
{names : name Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _81_195 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _81_195.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _175_562 = (find_name env x)
in _175_562.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _81_211 -> begin
(let _175_570 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _175_570))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _81_224 -> (match (_81_224) with
| ((name, _81_220), _81_223) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _81_226 -> (match (_81_226) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _81_235 = m
in (match (_81_235) with
| ((prefix, final), _81_232, _81_234) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _81_245 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _175_605 = (translate_module m)
in Some (_175_605)))
end)
with
| e -> begin
(

let _81_241 = (let _175_607 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _175_607))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _81_251 -> (match (_81_251) with
| (module_name, modul, _81_250) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _81_258 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let _81_320 = ()
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

let rec find_return_type = (fun _81_4 -> (match (_81_4) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_81_334, _81_336, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _175_614 = (find_return_type t0)
in (translate_type env _175_614))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in if (flavor = FStar_Extraction_ML_Syntax.Assumed) then begin
(let _175_617 = (let _175_616 = (let _175_615 = (translate_type env t0)
in ((name), (_175_615)))
in DExternal (_175_616))
in Some (_175_617))
end else begin
(

let body = (translate_expr env body)
in Some (DFunction (((t), (name), (binders), (body)))))
end))))))
end)
with
| e -> begin
(

let _81_326 = (let _175_619 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _175_619))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _81_358); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _81_351; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _81_348})::[]) -> begin
(

let _81_364 = ()
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

let _81_370 = (let _175_622 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _175_622))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (_81_378, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _81_390); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _81_386; FStar_Extraction_ML_Syntax.mllb_def = _81_384; FStar_Extraction_ML_Syntax.print_typ = _81_382})::_81_380) -> begin
(

let _81_396 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _81_403 = (match (ts) with
| Some (idents, t) -> begin
(let _175_625 = (let _175_623 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _175_623))
in (let _175_624 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _175_625 _175_624)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_81_406) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_81_409) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _175_628 = (let _175_627 = (let _175_626 = (translate_type env t)
in ((name), (_175_626)))
in DTypeAlias (_175_627))
in Some (_175_628)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _175_634 = (let _175_633 = (let _175_632 = (FStar_List.map (fun _81_431 -> (match (_81_431) with
| (f, t) -> begin
(let _175_631 = (let _175_630 = (translate_type env t)
in ((_175_630), (false)))
in ((f), (_175_631)))
end)) fields)
in ((name), (_175_632)))
in DTypeFlat (_175_633))
in Some (_175_634)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, _81_436, _81_438))::_81_433) -> begin
(

let _81_442 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _81_446 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_81_449) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_81_452) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_81_460) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _81_464, t2) -> begin
(let _175_639 = (let _175_638 = (translate_type env t1)
in (let _175_637 = (translate_type env t2)
in ((_175_638), (_175_637))))
in TArrow (_175_639))
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
(let _175_640 = (translate_type env arg)
in TBuf (_175_640))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_81_514)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_81_520, (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_81_527) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _81_537 -> (match (_81_537) with
| ((name, _81_534), typ) -> begin
(let _175_645 = (translate_type env typ)
in {name = name; typ = _175_645; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _81_546) -> begin
(let _175_648 = (find env name)
in EBound (_175_648))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _175_651 = (let _175_650 = (FStar_Util.must (mk_op op))
in (let _175_649 = (FStar_Util.must (mk_width m))
in ((_175_650), (_175_649))))
in EOp (_175_651))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _175_653 = (let _175_652 = (FStar_Util.must (mk_bool_op op))
in ((_175_652), (Bool)))
in EOp (_175_653))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _81_572); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _81_602 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _175_657 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HyperStack.stackref") -> begin
t
end
| _81_586 -> begin
(let _175_655 = (let _175_654 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _175_654))
in (FStar_All.failwith _175_655))
end)
in (let _175_656 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_81_592, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _81_590; FStar_Extraction_ML_Syntax.loc = _81_588} -> begin
body
end
| _81_599 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_175_657), (_175_656))))
end else begin
((typ), (body))
end
in (match (_81_602) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _175_658 = (translate_type env typ)
in {name = name; typ = _175_658; mut = is_mut})
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
in (let _175_661 = (let _175_660 = (translate_expr env expr)
in (let _175_659 = (translate_branches env t_scrut branches)
in ((_175_660), (_175_659))))
in EMatch (_175_661)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_616; FStar_Extraction_ML_Syntax.loc = _81_614}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _81_626); FStar_Extraction_ML_Syntax.mlty = _81_623; FStar_Extraction_ML_Syntax.loc = _81_621})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _175_662 = (find env v)
in EBound (_175_662))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_636; FStar_Extraction_ML_Syntax.loc = _81_634}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _81_647); FStar_Extraction_ML_Syntax.mlty = _81_644; FStar_Extraction_ML_Syntax.loc = _81_642})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _175_666 = (let _175_665 = (let _175_663 = (find env v)
in EBound (_175_663))
in (let _175_664 = (translate_expr env e)
in ((_175_665), (_175_664))))
in EAssign (_175_666))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_657; FStar_Extraction_ML_Syntax.loc = _81_655}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _175_669 = (let _175_668 = (translate_expr env e1)
in (let _175_667 = (translate_expr env e2)
in ((_175_668), (_175_667))))
in EBufRead (_175_669))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_669; FStar_Extraction_ML_Syntax.loc = _81_667}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _175_672 = (let _175_671 = (translate_expr env e1)
in (let _175_670 = (translate_expr env e2)
in ((_175_671), (_175_670))))
in EBufCreate (_175_672))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_681; FStar_Extraction_ML_Syntax.loc = _81_679}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _81_709 -> begin
(FStar_All.failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (let _175_679 = (let _175_678 = (list_elements e2)
in (FStar_List.map (translate_expr env) _175_678))
in EBufCreateL (_175_679))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_714; FStar_Extraction_ML_Syntax.loc = _81_712}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _175_682 = (let _175_681 = (translate_expr env e1)
in (let _175_680 = (translate_expr env e2)
in ((_175_681), (_175_680))))
in EBufSub (_175_682))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_727; FStar_Extraction_ML_Syntax.loc = _81_725}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _175_685 = (let _175_684 = (translate_expr env e1)
in (let _175_683 = (translate_expr env e2)
in ((_175_684), (_175_683))))
in EBufSub (_175_685))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_739; FStar_Extraction_ML_Syntax.loc = _81_737}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _175_689 = (let _175_688 = (translate_expr env e1)
in (let _175_687 = (translate_expr env e2)
in (let _175_686 = (translate_expr env e3)
in ((_175_688), (_175_687), (_175_686)))))
in EBufWrite (_175_689))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_752; FStar_Extraction_ML_Syntax.loc = _81_750}, (_81_757)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_764; FStar_Extraction_ML_Syntax.loc = _81_762}, (_81_769)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_776; FStar_Extraction_ML_Syntax.loc = _81_774}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _175_695 = (let _175_694 = (translate_expr env e1)
in (let _175_693 = (translate_expr env e2)
in (let _175_692 = (translate_expr env e3)
in (let _175_691 = (translate_expr env e4)
in (let _175_690 = (translate_expr env e5)
in ((_175_694), (_175_693), (_175_692), (_175_691), (_175_690)))))))
in EBufBlit (_175_695))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _81_791; FStar_Extraction_ML_Syntax.loc = _81_789}, (_81_796)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _81_803; FStar_Extraction_ML_Syntax.loc = _81_801}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _175_697 = (FStar_Util.must (mk_width m))
in (let _175_696 = (FStar_Util.must (mk_op op))
in (mk_op_app env _175_697 _175_696 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _81_817; FStar_Extraction_ML_Syntax.loc = _81_815}, args) when (is_bool_op op) -> begin
(let _175_698 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _175_698 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _175_700 = (let _175_699 = (FStar_Util.must (mk_width m))
in ((_175_699), (c)))
in EConstant (_175_700))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _81_876; FStar_Extraction_ML_Syntax.loc = _81_874}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _175_702 = (let _175_701 = (translate_expr env arg)
in ((_175_701), (TInt (UInt64))))
in ECast (_175_702))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _175_704 = (let _175_703 = (translate_expr env arg)
in ((_175_703), (TInt (UInt32))))
in ECast (_175_704))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _175_706 = (let _175_705 = (translate_expr env arg)
in ((_175_705), (TInt (UInt16))))
in ECast (_175_706))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _175_708 = (let _175_707 = (translate_expr env arg)
in ((_175_707), (TInt (UInt8))))
in ECast (_175_708))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _175_710 = (let _175_709 = (translate_expr env arg)
in ((_175_709), (TInt (Int64))))
in ECast (_175_710))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _175_712 = (let _175_711 = (translate_expr env arg)
in ((_175_711), (TInt (Int32))))
in ECast (_175_712))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _175_714 = (let _175_713 = (translate_expr env arg)
in ((_175_713), (TInt (Int16))))
in ECast (_175_714))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _175_716 = (let _175_715 = (translate_expr env arg)
in ((_175_715), (TInt (Int8))))
in ECast (_175_716))
end else begin
(let _175_717 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _175_717))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _81_892; FStar_Extraction_ML_Syntax.loc = _81_890}, args) -> begin
(let _175_719 = (let _175_718 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_175_718)))
in EApp (_175_719))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _175_722 = (let _175_721 = (translate_expr env e)
in (let _175_720 = (translate_type env t_to)
in ((_175_721), (_175_720))))
in ECast (_175_722))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_81_907, fields) -> begin
(let _175_727 = (let _175_726 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _175_725 = (FStar_List.map (fun _81_913 -> (match (_81_913) with
| (field, expr) -> begin
(let _175_724 = (translate_expr env expr)
in ((field), (_175_724)))
end)) fields)
in ((_175_726), (_175_725))))
in EFlat (_175_727))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _175_730 = (let _175_729 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _175_728 = (translate_expr env e)
in ((_175_729), (_175_728), ((Prims.snd path)))))
in EField (_175_730))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_81_919) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _81_923) -> begin
(let _175_732 = (let _175_731 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _175_731))
in (FStar_All.failwith _175_732))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_81_927) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_81_930) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _175_733 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_175_733))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_81_935) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_81_938) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_81_941) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_81_944) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_81_947) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : FStar_Extraction_ML_Syntax.mlty  ->  lident = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], lid) -> begin
lid
end
| _81_955 -> begin
(FStar_All.failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t_scrut branches -> (FStar_List.map (translate_branch env t_scrut) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t_scrut _81_964 -> (match (_81_964) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _81_967 = (translate_pat env t_scrut pat)
in (match (_81_967) with
| (env, pat) -> begin
(let _175_741 = (translate_expr env expr)
in ((pat), (_175_741)))
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, _81_978) -> begin
(

let env = (extend env name false)
in (let _175_747 = (let _175_746 = (let _175_745 = (translate_type env t)
in {name = name; typ = _175_745; mut = false})
in PVar (_175_746))
in ((env), (_175_747))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_81_984) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_81_987) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_81_990) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_81_993) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_81_996) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_81_1004)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_81_1009) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_81_1012) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_81_1015) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_81_1018) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_81_1021, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _175_754 = (let _175_753 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_175_753)))
in EApp (_175_754)))




