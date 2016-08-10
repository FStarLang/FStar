
open Prims

type decl =
| DFunction of (typ * ident * binder Prims.list * expr)
| DTypeAlias of (ident * typ)
| DGlobal of (ident * typ * expr) 
 and expr =
| EBound of var
| EOpen of binder
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
{name : ident; typ : typ; mut : Prims.bool; mark : Prims.int} 
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
| DFunction (_80_11) -> begin
_80_11
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_80_14) -> begin
_80_14
end))


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_80_17) -> begin
_80_17
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_80_20) -> begin
_80_20
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_80_23) -> begin
_80_23
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_80_26) -> begin
_80_26
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_80_29) -> begin
_80_29
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_80_32) -> begin
_80_32
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_80_35) -> begin
_80_35
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_80_38) -> begin
_80_38
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_80_41) -> begin
_80_41
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_80_44) -> begin
_80_44
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_80_47) -> begin
_80_47
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_80_50) -> begin
_80_50
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_80_53) -> begin
_80_53
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_80_56) -> begin
_80_56
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_80_59) -> begin
_80_59
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_80_62) -> begin
_80_62
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_80_65) -> begin
_80_65
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_80_68) -> begin
_80_68
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_80_71) -> begin
_80_71
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_80_74) -> begin
_80_74
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_80_77) -> begin
_80_77
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_80_81) -> begin
_80_81
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_80_84) -> begin
_80_84
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_80_87) -> begin
_80_87
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_80_90) -> begin
_80_90
end))


type version =
Prims.int


let current_version : version = 6


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _80_96 -> (match (_80_96) with
| (x, _80_93, _80_95) -> begin
x
end))


let snd3 = (fun _80_102 -> (match (_80_102) with
| (_80_98, x, _80_101) -> begin
x
end))


let thd3 = (fun _80_108 -> (match (_80_108) with
| (_80_104, _80_106, x) -> begin
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
| _80_119 -> begin
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
| _80_127 -> begin
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
| _80_165 -> begin
None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))


type env =
{names : name Prims.list; module_name : Prims.string} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string  ->  env = (fun module_name -> {names = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _80_178 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _80_178.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _172_477 = (find_name env x)
in _172_477.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _80_194 -> begin
(let _172_485 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _172_485))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _80_207 -> (match (_80_207) with
| ((name, _80_203), _80_206) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _80_209 -> (match (_80_209) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> try
(match (()) with
| () -> begin
(

let _80_219 = (FStar_Util.print1 "Attempting to translate module %s\n" (fst3 m))
in (let _172_519 = (translate_module m)
in Some (_172_519)))
end)
with
| e -> begin
(

let _80_215 = (let _172_521 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" (fst3 m) _172_521))
in None)
end) modules)
end))
and translate_module : (Prims.string * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _80_225 -> (match (_80_225) with
| (module_name, modul, _80_224) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _80_231 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in ((module_name), (program)))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_258); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_80_248, _80_250, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _80_245; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = fun_body; FStar_Extraction_ML_Syntax.mlty = _80_241; FStar_Extraction_ML_Syntax.loc = _80_239}; FStar_Extraction_ML_Syntax.print_typ = _80_237})::[]) -> begin
(match (fun_body) with
| (FStar_Extraction_ML_Syntax.MLE_Fun (args, body)) | (FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _)) -> begin
(

let _80_281 = ()
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
| FStar_Extraction_ML_Syntax.MLTY_Fun (_80_295, _80_297, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _172_528 = (find_return_type t)
in (translate_type env _172_528))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let body = (translate_expr env body)
in (

let name = (Prims.strcat env.module_name (Prims.strcat "_" name))
in Some (DFunction (((t), (name), (binders), (body)))))))))))
end)
with
| e -> begin
(

let _80_287 = (let _172_530 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _172_530))
in None)
end)
end
| _80_308 -> begin
(

let _80_309 = (FStar_Util.print_string "Unexpected body for a function type\n")
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_323); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _80_316; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _80_313})::[]) -> begin
(

let _80_329 = ()
in try
(match (()) with
| () -> begin
(

let t = (translate_type env t)
in (

let expr = (translate_expr env expr)
in (

let name = (Prims.strcat env.module_name (Prims.strcat "_" name))
in Some (DGlobal (((name), (t), (expr)))))))
end)
with
| e -> begin
(

let _80_335 = (let _172_533 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _172_533))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (_80_343, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_355); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_351; FStar_Extraction_ML_Syntax.mllb_def = _80_349; FStar_Extraction_ML_Syntax.print_typ = _80_347})::_80_345) -> begin
(

let _80_361 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _80_368 = (match (ts) with
| Some (idents, t) -> begin
(let _172_536 = (let _172_534 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _172_534))
in (let _172_535 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _172_536 _172_535)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_80_371) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_80_374) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = (Prims.strcat env.module_name (Prims.strcat "_" name))
in (let _172_539 = (let _172_538 = (let _172_537 = (translate_type env t)
in ((name), (_172_537)))
in DTypeAlias (_172_538))
in Some (_172_539)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, _80_389, _80_391))::_80_386) -> begin
(

let _80_395 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _80_399 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_80_402) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_80_405) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_80_413) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _80_417, t2) -> begin
(let _172_544 = (let _172_543 = (translate_type env t1)
in (let _172_542 = (translate_type env t2)
in ((_172_543), (_172_542))))
in TArrow (_172_544))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.int") -> begin
(FStar_All.failwith "todo: translate_type [Prims.int]")
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
(let _172_545 = (translate_type env arg)
in TBuf (_172_545))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HyperStack.mem") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_80_475)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_80_481, (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_80_488) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _80_498 -> (match (_80_498) with
| ((name, _80_495), typ) -> begin
(let _172_550 = (translate_type env typ)
in {name = name; typ = _172_550; mut = false; mark = 0})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _80_507) -> begin
(let _172_553 = (find env name)
in EBound (_172_553))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_556 = (let _172_555 = (FStar_Util.must (mk_op op))
in (let _172_554 = (FStar_Util.must (mk_width m))
in ((_172_555), (_172_554))))
in EOp (_172_556))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _172_558 = (let _172_557 = (FStar_Util.must (mk_bool_op op))
in ((_172_557), (Bool)))
in EOp (_172_558))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_533); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _80_563 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _172_560 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.salloc") -> begin
t
end
| _80_547 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _172_559 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_80_553, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _80_551; FStar_Extraction_ML_Syntax.loc = _80_549} -> begin
body
end
| _80_560 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_172_560), (_172_559))))
end else begin
((typ), (body))
end
in (match (_80_563) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _172_561 = (translate_type env typ)
in {name = name; typ = _172_561; mut = is_mut; mark = 0})
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
in (let _172_564 = (let _172_563 = (translate_expr env expr)
in (let _172_562 = (translate_branches env t branches)
in ((_172_563), (_172_562))))
in EMatch (_172_564)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_577; FStar_Extraction_ML_Syntax.loc = _80_575}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _80_587); FStar_Extraction_ML_Syntax.mlty = _80_584; FStar_Extraction_ML_Syntax.loc = _80_582})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _172_565 = (find env v)
in EBound (_172_565))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_597; FStar_Extraction_ML_Syntax.loc = _80_595}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _80_608); FStar_Extraction_ML_Syntax.mlty = _80_605; FStar_Extraction_ML_Syntax.loc = _80_603})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _172_569 = (let _172_568 = (let _172_566 = (find env v)
in EBound (_172_566))
in (let _172_567 = (translate_expr env e)
in ((_172_568), (_172_567))))
in EAssign (_172_569))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_618; FStar_Extraction_ML_Syntax.loc = _80_616}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") -> begin
(let _172_572 = (let _172_571 = (translate_expr env e1)
in (let _172_570 = (translate_expr env e2)
in ((_172_571), (_172_570))))
in EBufRead (_172_572))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_630; FStar_Extraction_ML_Syntax.loc = _80_628}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _172_575 = (let _172_574 = (translate_expr env e1)
in (let _172_573 = (translate_expr env e2)
in ((_172_574), (_172_573))))
in EBufCreate (_172_575))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_642; FStar_Extraction_ML_Syntax.loc = _80_640}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _172_578 = (let _172_577 = (translate_expr env e1)
in (let _172_576 = (translate_expr env e2)
in ((_172_577), (_172_576))))
in EBufSub (_172_578))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_655; FStar_Extraction_ML_Syntax.loc = _80_653}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _172_581 = (let _172_580 = (translate_expr env e1)
in (let _172_579 = (translate_expr env e2)
in ((_172_580), (_172_579))))
in EBufSub (_172_581))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_667; FStar_Extraction_ML_Syntax.loc = _80_665}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") -> begin
(let _172_585 = (let _172_584 = (translate_expr env e1)
in (let _172_583 = (translate_expr env e2)
in (let _172_582 = (translate_expr env e3)
in ((_172_584), (_172_583), (_172_582)))))
in EBufWrite (_172_585))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_680; FStar_Extraction_ML_Syntax.loc = _80_678}, (_80_685)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_692; FStar_Extraction_ML_Syntax.loc = _80_690}, (_80_697)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_704; FStar_Extraction_ML_Syntax.loc = _80_702}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _172_591 = (let _172_590 = (translate_expr env e1)
in (let _172_589 = (translate_expr env e2)
in (let _172_588 = (translate_expr env e3)
in (let _172_587 = (translate_expr env e4)
in (let _172_586 = (translate_expr env e5)
in ((_172_590), (_172_589), (_172_588), (_172_587), (_172_586)))))))
in EBufBlit (_172_591))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_719; FStar_Extraction_ML_Syntax.loc = _80_717}, (_80_724)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.get") -> begin
EConstant (((UInt8), ("0")))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _80_731; FStar_Extraction_ML_Syntax.loc = _80_729}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_593 = (FStar_Util.must (mk_width m))
in (let _172_592 = (FStar_Util.must (mk_op op))
in (mk_op_app env _172_593 _172_592 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _80_745; FStar_Extraction_ML_Syntax.loc = _80_743}, args) when (is_bool_op op) -> begin
(let _172_594 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _172_594 args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _80_758; FStar_Extraction_ML_Syntax.loc = _80_756}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _80_769; FStar_Extraction_ML_Syntax.loc = _80_767})::[]) when (is_machine_int m) -> begin
(let _172_596 = (let _172_595 = (FStar_Util.must (mk_width m))
in ((_172_595), (c)))
in EConstant (_172_596))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _80_782; FStar_Extraction_ML_Syntax.loc = _80_780}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _172_598 = (let _172_597 = (translate_expr env arg)
in ((_172_597), (TInt (UInt64))))
in ECast (_172_598))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _172_600 = (let _172_599 = (translate_expr env arg)
in ((_172_599), (TInt (UInt32))))
in ECast (_172_600))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _172_602 = (let _172_601 = (translate_expr env arg)
in ((_172_601), (TInt (UInt16))))
in ECast (_172_602))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _172_604 = (let _172_603 = (translate_expr env arg)
in ((_172_603), (TInt (UInt8))))
in ECast (_172_604))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _172_606 = (let _172_605 = (translate_expr env arg)
in ((_172_605), (TInt (Int64))))
in ECast (_172_606))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _172_608 = (let _172_607 = (translate_expr env arg)
in ((_172_607), (TInt (Int32))))
in ECast (_172_608))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _172_610 = (let _172_609 = (translate_expr env arg)
in ((_172_609), (TInt (Int16))))
in ECast (_172_610))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _172_612 = (let _172_611 = (translate_expr env arg)
in ((_172_611), (TInt (Int8))))
in ECast (_172_612))
end else begin
(let _172_613 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _172_613))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _80_798; FStar_Extraction_ML_Syntax.loc = _80_796}, args) -> begin
(let _172_615 = (let _172_614 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_172_614)))
in EApp (_172_615))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _172_618 = (let _172_617 = (translate_expr env e)
in (let _172_616 = (translate_type env t_to)
in ((_172_617), (_172_616))))
in ECast (_172_618))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_80_813) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (_80_816) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_80_819) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_80_822) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _172_619 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_172_619))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_80_827) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_80_830) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_80_833) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_80_836) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_80_839) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_80_842) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_80_845) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t branches -> (FStar_List.map (translate_branch env t) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t _80_855 -> (match (_80_855) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _80_858 = (translate_pat env t pat)
in (match (_80_858) with
| (env, pat) -> begin
(let _172_626 = (translate_expr env expr)
in ((pat), (_172_626)))
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, _80_869) -> begin
(

let env = (extend env name false)
in (let _172_632 = (let _172_631 = (let _172_630 = (translate_type env t)
in {name = name; typ = _172_630; mut = false; mark = 0})
in PVar (_172_631))
in ((env), (_172_632))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_80_875) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_80_878) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_80_881) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_80_884) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_80_887) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_80_895)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_80_900) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_80_903) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_80_906) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_80_909) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_80_912, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _172_639 = (let _172_638 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_172_638)))
in EApp (_172_639)))




