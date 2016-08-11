
open Prims

type decl =
| DFunction of (typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * typ)
| DGlobal of (lident * typ * expr) 
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
 and binder =
{name : ident; typ : typ; mut : Prims.bool; mark : Prims.int; meta : meta Prims.option} 
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


let is_EBound = (fun _discr_ -> (match (_discr_) with
| EBound (_) -> begin
true
end
| _ -> begin
false
end))


let is_EOpen = (fun _discr_ -> (match (_discr_) with
| EOpen (_) -> begin
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


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))


let is_MetaSequence = (fun _discr_ -> (match (_discr_) with
| MetaSequence (_) -> begin
true
end
| _ -> begin
false
end))


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
| DFunction (_80_12) -> begin
_80_12
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_80_15) -> begin
_80_15
end))


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_80_18) -> begin
_80_18
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_80_21) -> begin
_80_21
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_80_24) -> begin
_80_24
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_80_27) -> begin
_80_27
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_80_30) -> begin
_80_30
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_80_33) -> begin
_80_33
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_80_36) -> begin
_80_36
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_80_39) -> begin
_80_39
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_80_42) -> begin
_80_42
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_80_45) -> begin
_80_45
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_80_48) -> begin
_80_48
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_80_51) -> begin
_80_51
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_80_54) -> begin
_80_54
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_80_57) -> begin
_80_57
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_80_60) -> begin
_80_60
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_80_63) -> begin
_80_63
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_80_66) -> begin
_80_66
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_80_69) -> begin
_80_69
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_80_72) -> begin
_80_72
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_80_75) -> begin
_80_75
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_80_78) -> begin
_80_78
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_80_82) -> begin
_80_82
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_80_85) -> begin
_80_85
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_80_88) -> begin
_80_88
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_80_91) -> begin
_80_91
end))


type version =
Prims.int


let current_version : version = 8


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _80_97 -> (match (_80_97) with
| (x, _80_94, _80_96) -> begin
x
end))


let snd3 = (fun _80_103 -> (match (_80_103) with
| (_80_99, x, _80_102) -> begin
x
end))


let thd3 = (fun _80_109 -> (match (_80_109) with
| (_80_105, _80_107, x) -> begin
x
end))


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
| _80_120 -> begin
None
end))


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
| _80_128 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


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
| _80_166 -> begin
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

let _80_179 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _80_179.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _172_483 = (find_name env x)
in _172_483.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _80_195 -> begin
(let _172_491 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _172_491))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _80_208 -> (match (_80_208) with
| ((name, _80_204), _80_207) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _80_210 -> (match (_80_210) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _80_219 = m
in (match (_80_219) with
| ((prefix, final), _80_216, _80_218) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _80_229 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _172_525 = (translate_module m)
in Some (_172_525)))
end)
with
| e -> begin
(

let _80_225 = (let _172_527 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _172_527))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _80_235 -> (match (_80_235) with
| (module_name, modul, _80_234) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _80_242 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_, _, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_, _, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let _80_316 = ()
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

let rec find_return_type = (fun _80_4 -> (match (_80_4) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_80_330, _80_332, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _172_534 = (find_return_type t)
in (translate_type env _172_534))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let body = if (flavor = FStar_Extraction_ML_Syntax.Assumed) then begin
EAbort
end else begin
(translate_expr env body)
end
in (

let name = ((env.module_name), (name))
in Some (DFunction (((t), (name), (binders), (body)))))))))))
end)
with
| e -> begin
(

let _80_322 = (let _172_536 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _172_536))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_354); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _80_347; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _80_344})::[]) -> begin
(

let _80_360 = ()
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

let _80_366 = (let _172_539 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _172_539))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (_80_374, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_386); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_382; FStar_Extraction_ML_Syntax.mllb_def = _80_380; FStar_Extraction_ML_Syntax.print_typ = _80_378})::_80_376) -> begin
(

let _80_392 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _80_399 = (match (ts) with
| Some (idents, t) -> begin
(let _172_542 = (let _172_540 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _172_540))
in (let _172_541 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _172_542 _172_541)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_80_402) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_80_405) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _172_545 = (let _172_544 = (let _172_543 = (translate_type env t)
in ((name), (_172_543)))
in DTypeAlias (_172_544))
in Some (_172_545)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, _80_420, _80_422))::_80_417) -> begin
(

let _80_426 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _80_430 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_80_433) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_80_436) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_80_444) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _80_448, t2) -> begin
(let _172_550 = (let _172_549 = (translate_type env t1)
in (let _172_548 = (translate_type env t2)
in ((_172_549), (_172_548))))
in TArrow (_172_550))
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
(let _172_551 = (translate_type env arg)
in TBuf (_172_551))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_80_498)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_80_504, (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_80_511) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _80_521 -> (match (_80_521) with
| ((name, _80_518), typ) -> begin
(let _172_556 = (translate_type env typ)
in {name = name; typ = _172_556; mut = false; mark = 0; meta = None})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _80_530) -> begin
(let _172_559 = (find env name)
in EBound (_172_559))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_562 = (let _172_561 = (FStar_Util.must (mk_op op))
in (let _172_560 = (FStar_Util.must (mk_width m))
in ((_172_561), (_172_560))))
in EOp (_172_562))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _172_564 = (let _172_563 = (FStar_Util.must (mk_bool_op op))
in ((_172_563), (Bool)))
in EOp (_172_564))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_556); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _80_586 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _172_566 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.salloc") -> begin
t
end
| _80_570 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _172_565 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_80_576, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _80_574; FStar_Extraction_ML_Syntax.loc = _80_572} -> begin
body
end
| _80_583 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_172_566), (_172_565))))
end else begin
((typ), (body))
end
in (match (_80_586) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _172_567 = (translate_type env typ)
in {name = name; typ = _172_567; mut = is_mut; mark = 0; meta = None})
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

let t = expr.FStar_Extraction_ML_Syntax.mlty
in (let _172_571 = (let _172_570 = (translate_expr env expr)
in (let _172_569 = (translate_branches env t branches)
in (let _172_568 = (translate_type env t)
in ((_172_570), (_172_569), (_172_568)))))
in EMatch (_172_571)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_600; FStar_Extraction_ML_Syntax.loc = _80_598}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _80_610); FStar_Extraction_ML_Syntax.mlty = _80_607; FStar_Extraction_ML_Syntax.loc = _80_605})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _172_572 = (find env v)
in EBound (_172_572))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_620; FStar_Extraction_ML_Syntax.loc = _80_618}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _80_631); FStar_Extraction_ML_Syntax.mlty = _80_628; FStar_Extraction_ML_Syntax.loc = _80_626})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _172_576 = (let _172_575 = (let _172_573 = (find env v)
in EBound (_172_573))
in (let _172_574 = (translate_expr env e)
in ((_172_575), (_172_574))))
in EAssign (_172_576))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_641; FStar_Extraction_ML_Syntax.loc = _80_639}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") -> begin
(let _172_579 = (let _172_578 = (translate_expr env e1)
in (let _172_577 = (translate_expr env e2)
in ((_172_578), (_172_577))))
in EBufRead (_172_579))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_653; FStar_Extraction_ML_Syntax.loc = _80_651}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _172_582 = (let _172_581 = (translate_expr env e1)
in (let _172_580 = (translate_expr env e2)
in ((_172_581), (_172_580))))
in EBufCreate (_172_582))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_665; FStar_Extraction_ML_Syntax.loc = _80_663}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _172_585 = (let _172_584 = (translate_expr env e1)
in (let _172_583 = (translate_expr env e2)
in ((_172_584), (_172_583))))
in EBufSub (_172_585))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_678; FStar_Extraction_ML_Syntax.loc = _80_676}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _172_588 = (let _172_587 = (translate_expr env e1)
in (let _172_586 = (translate_expr env e2)
in ((_172_587), (_172_586))))
in EBufSub (_172_588))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_690; FStar_Extraction_ML_Syntax.loc = _80_688}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") -> begin
(let _172_592 = (let _172_591 = (translate_expr env e1)
in (let _172_590 = (translate_expr env e2)
in (let _172_589 = (translate_expr env e3)
in ((_172_591), (_172_590), (_172_589)))))
in EBufWrite (_172_592))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_703; FStar_Extraction_ML_Syntax.loc = _80_701}, (_80_708)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_715; FStar_Extraction_ML_Syntax.loc = _80_713}, (_80_720)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_727; FStar_Extraction_ML_Syntax.loc = _80_725}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _172_598 = (let _172_597 = (translate_expr env e1)
in (let _172_596 = (translate_expr env e2)
in (let _172_595 = (translate_expr env e3)
in (let _172_594 = (translate_expr env e4)
in (let _172_593 = (translate_expr env e5)
in ((_172_597), (_172_596), (_172_595), (_172_594), (_172_593)))))))
in EBufBlit (_172_598))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_742; FStar_Extraction_ML_Syntax.loc = _80_740}, (_80_747)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.get") -> begin
EConstant (((UInt8), ("0")))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _80_754; FStar_Extraction_ML_Syntax.loc = _80_752}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_600 = (FStar_Util.must (mk_width m))
in (let _172_599 = (FStar_Util.must (mk_op op))
in (mk_op_app env _172_600 _172_599 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _80_768; FStar_Extraction_ML_Syntax.loc = _80_766}, args) when (is_bool_op op) -> begin
(let _172_601 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _172_601 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _172_603 = (let _172_602 = (FStar_Util.must (mk_width m))
in ((_172_602), (c)))
in EConstant (_172_603))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _80_827; FStar_Extraction_ML_Syntax.loc = _80_825}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _172_605 = (let _172_604 = (translate_expr env arg)
in ((_172_604), (TInt (UInt64))))
in ECast (_172_605))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _172_607 = (let _172_606 = (translate_expr env arg)
in ((_172_606), (TInt (UInt32))))
in ECast (_172_607))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _172_609 = (let _172_608 = (translate_expr env arg)
in ((_172_608), (TInt (UInt16))))
in ECast (_172_609))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _172_611 = (let _172_610 = (translate_expr env arg)
in ((_172_610), (TInt (UInt8))))
in ECast (_172_611))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _172_613 = (let _172_612 = (translate_expr env arg)
in ((_172_612), (TInt (Int64))))
in ECast (_172_613))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _172_615 = (let _172_614 = (translate_expr env arg)
in ((_172_614), (TInt (Int32))))
in ECast (_172_615))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _172_617 = (let _172_616 = (translate_expr env arg)
in ((_172_616), (TInt (Int16))))
in ECast (_172_617))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _172_619 = (let _172_618 = (translate_expr env arg)
in ((_172_618), (TInt (Int8))))
in ECast (_172_619))
end else begin
(let _172_620 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _172_620))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _80_843; FStar_Extraction_ML_Syntax.loc = _80_841}, args) -> begin
(let _172_622 = (let _172_621 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_172_621)))
in EApp (_172_622))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _172_625 = (let _172_624 = (translate_expr env e)
in (let _172_623 = (translate_type env t_to)
in ((_172_624), (_172_623))))
in ECast (_172_625))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_80_858) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (_80_861) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_80_864) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_80_867) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _172_626 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_172_626))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_80_872) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_80_875) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_80_878) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_80_881) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_80_884) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_80_887) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_80_890) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t branches -> (FStar_List.map (translate_branch env t) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t _80_900 -> (match (_80_900) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _80_903 = (translate_pat env t pat)
in (match (_80_903) with
| (env, pat) -> begin
(let _172_633 = (translate_expr env expr)
in ((pat), (_172_633)))
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, _80_914) -> begin
(

let env = (extend env name false)
in (let _172_639 = (let _172_638 = (let _172_637 = (translate_type env t)
in {name = name; typ = _172_637; mut = false; mark = 0; meta = None})
in PVar (_172_638))
in ((env), (_172_639))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_80_920) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_80_923) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_80_926) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_80_929) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_80_932) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_80_940)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_80_945) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_80_948) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_80_951) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_80_954) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_80_957, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _172_646 = (let _172_645 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_172_645)))
in EApp (_172_646)))




