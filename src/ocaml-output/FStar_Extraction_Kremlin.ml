
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
| DFunction (_79_10) -> begin
_79_10
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_79_13) -> begin
_79_13
end))


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_79_16) -> begin
_79_16
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_79_19) -> begin
_79_19
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_79_22) -> begin
_79_22
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_79_25) -> begin
_79_25
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_79_28) -> begin
_79_28
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_79_31) -> begin
_79_31
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_79_34) -> begin
_79_34
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_79_37) -> begin
_79_37
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_79_40) -> begin
_79_40
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_79_43) -> begin
_79_43
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_79_46) -> begin
_79_46
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_79_49) -> begin
_79_49
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_79_52) -> begin
_79_52
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_79_55) -> begin
_79_55
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_79_58) -> begin
_79_58
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_79_61) -> begin
_79_61
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_79_64) -> begin
_79_64
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_79_67) -> begin
_79_67
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_79_70) -> begin
_79_70
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_79_73) -> begin
_79_73
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_79_77) -> begin
_79_77
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_79_80) -> begin
_79_80
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_79_83) -> begin
_79_83
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_79_86) -> begin
_79_86
end))


type version =
Prims.int


let current_version : version = 4


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _79_92 -> (match (_79_92) with
| (x, _79_89, _79_91) -> begin
x
end))


let snd3 = (fun _79_98 -> (match (_79_98) with
| (_79_94, x, _79_97) -> begin
x
end))


let thd3 = (fun _79_104 -> (match (_79_104) with
| (_79_100, _79_102, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun _79_1 -> (match (_79_1) with
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
| _79_115 -> begin
None
end))


let mk_op : Prims.string  ->  op Prims.option = (fun _79_2 -> (match (_79_2) with
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
| _79_144 -> begin
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

let _79_157 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _79_157.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _170_449 = (find_name env x)
in _170_449.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _79_173 -> begin
(let _170_457 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _170_457))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _79_186 -> (match (_79_186) with
| ((name, _79_182), _79_185) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _79_188 -> (match (_79_188) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> try
(match (()) with
| () -> begin
(

let _79_198 = (FStar_Util.print1 "Attempting to translate module %s\n" (fst3 m))
in (let _170_491 = (translate_module m)
in Some (_170_491)))
end)
with
| e -> begin
(

let _79_194 = (let _170_493 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" (fst3 m) _170_493))
in None)
end) modules)
end))
and translate_module : (Prims.string * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _79_204 -> (match (_79_204) with
| (module_name, modul, _79_203) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _79_210 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (module_name, program))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_240); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_79_230, _79_232, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _79_227; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _79_220; FStar_Extraction_ML_Syntax.loc = _79_218}; FStar_Extraction_ML_Syntax.print_typ = _79_216})::[]) -> begin
(

let _79_246 = ()
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

let rec find_return_type = (fun _79_3 -> (match (_79_3) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_260, _79_262, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _170_500 = (find_return_type t)
in (translate_type env _170_500))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let body = (translate_expr env body)
in (

let name = (Prims.strcat (Prims.strcat env.module_name "_") name)
in Some (DFunction ((t, name, binders, body))))))))))
end)
with
| e -> begin
(

let _79_252 = (let _170_502 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _170_502))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_284); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _79_277; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _79_274})::[]) -> begin
(

let _79_290 = ()
in try
(match (()) with
| () -> begin
(

let t = (translate_type env t)
in (

let expr = (translate_expr env expr)
in (

let name = (Prims.strcat (Prims.strcat env.module_name "_") name)
in Some (DGlobal ((name, t, expr))))))
end)
with
| e -> begin
(

let _79_296 = (let _170_505 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _170_505))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (_79_304, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_317); FStar_Extraction_ML_Syntax.mllb_tysc = _79_314; FStar_Extraction_ML_Syntax.mllb_add_unit = _79_312; FStar_Extraction_ML_Syntax.mllb_def = _79_310; FStar_Extraction_ML_Syntax.print_typ = _79_308})::_79_306) -> begin
(

let _79_323 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Let (_79_326) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_79_329) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = (Prims.strcat (Prims.strcat env.module_name "_") name)
in (let _170_508 = (let _170_507 = (let _170_506 = (translate_type env t)
in (name, _170_506))
in DTypeAlias (_170_507))
in Some (_170_508)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, _79_344, _79_346))::_79_341) -> begin
(

let _79_350 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_79_353) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_79_356) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_79_364) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _79_368, t2) -> begin
(let _170_513 = (let _170_512 = (translate_type env t1)
in (let _170_511 = (translate_type env t2)
in (_170_512, _170_511)))
in TArrow (_170_513))
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
(let _170_514 = (translate_type env arg)
in TBuf (_170_514))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HyperStack.mem") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_79_426)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified ((path, type_name))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_438, p) -> begin
(let _170_515 = (FStar_Util.format2 "todo: translate_type [MLTY_Named] %s (module_name = %s)" (FStar_Extraction_ML_Syntax.string_of_mlpath p) env.module_name)
in (FStar_All.failwith _170_515))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_79_443) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _79_453 -> (match (_79_453) with
| ((name, _79_450), typ) -> begin
(let _170_520 = (translate_type env typ)
in {name = name; typ = _170_520; mut = false; mark = 0})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _79_462) -> begin
(let _170_523 = (find env name)
in EBound (_170_523))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _170_526 = (let _170_525 = (FStar_Util.must (mk_op op))
in (let _170_524 = (FStar_Util.must (mk_width m))
in (_170_525, _170_524)))
in EOp (_170_526))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_483); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _79_513 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _170_528 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.salloc") -> begin
t
end
| _79_497 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _170_527 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_79_503, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _79_501; FStar_Extraction_ML_Syntax.loc = _79_499} -> begin
body
end
| _79_510 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (_170_528, _170_527)))
end else begin
(typ, body)
end
in (match (_79_513) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _170_529 = (translate_type env typ)
in {name = name; typ = _170_529; mut = is_mut; mark = 0})
in (

let body = (translate_expr env body)
in (

let env = (extend env name is_mut)
in (

let continuation = (translate_expr env continuation)
in ELet ((binder, body, continuation)))))))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(

let t = expr.FStar_Extraction_ML_Syntax.mlty
in (let _170_532 = (let _170_531 = (translate_expr env expr)
in (let _170_530 = (translate_branches env t branches)
in (_170_531, _170_530)))
in EMatch (_170_532)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_527; FStar_Extraction_ML_Syntax.loc = _79_525}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_537); FStar_Extraction_ML_Syntax.mlty = _79_534; FStar_Extraction_ML_Syntax.loc = _79_532})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _170_533 = (find env v)
in EBound (_170_533))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_547; FStar_Extraction_ML_Syntax.loc = _79_545}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_558); FStar_Extraction_ML_Syntax.mlty = _79_555; FStar_Extraction_ML_Syntax.loc = _79_553})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _170_537 = (let _170_536 = (let _170_534 = (find env v)
in EBound (_170_534))
in (let _170_535 = (translate_expr env e)
in (_170_536, _170_535)))
in EAssign (_170_537))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_568; FStar_Extraction_ML_Syntax.loc = _79_566}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") -> begin
(let _170_540 = (let _170_539 = (translate_expr env e1)
in (let _170_538 = (translate_expr env e2)
in (_170_539, _170_538)))
in EBufRead (_170_540))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_580; FStar_Extraction_ML_Syntax.loc = _79_578}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _170_543 = (let _170_542 = (translate_expr env e1)
in (let _170_541 = (translate_expr env e2)
in (_170_542, _170_541)))
in EBufCreate (_170_543))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_592; FStar_Extraction_ML_Syntax.loc = _79_590}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _170_546 = (let _170_545 = (translate_expr env e1)
in (let _170_544 = (translate_expr env e2)
in (_170_545, _170_544)))
in EBufSub (_170_546))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_605; FStar_Extraction_ML_Syntax.loc = _79_603}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _170_549 = (let _170_548 = (translate_expr env e1)
in (let _170_547 = (translate_expr env e2)
in (_170_548, _170_547)))
in EBufSub (_170_549))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_617; FStar_Extraction_ML_Syntax.loc = _79_615}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") -> begin
(let _170_553 = (let _170_552 = (translate_expr env e1)
in (let _170_551 = (translate_expr env e2)
in (let _170_550 = (translate_expr env e3)
in (_170_552, _170_551, _170_550))))
in EBufWrite (_170_553))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_630; FStar_Extraction_ML_Syntax.loc = _79_628}, (_79_635)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_642; FStar_Extraction_ML_Syntax.loc = _79_640}, (_79_647)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_654; FStar_Extraction_ML_Syntax.loc = _79_652}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _170_559 = (let _170_558 = (translate_expr env e1)
in (let _170_557 = (translate_expr env e2)
in (let _170_556 = (translate_expr env e3)
in (let _170_555 = (translate_expr env e4)
in (let _170_554 = (translate_expr env e5)
in (_170_558, _170_557, _170_556, _170_555, _170_554))))))
in EBufBlit (_170_559))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_669; FStar_Extraction_ML_Syntax.loc = _79_667}, (_79_674)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.get") -> begin
EConstant ((UInt8, "0"))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _79_681; FStar_Extraction_ML_Syntax.loc = _79_679}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _170_561 = (FStar_Util.must (mk_width m))
in (let _170_560 = (FStar_Util.must (mk_op op))
in (mk_op_app env _170_561 _170_560 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _79_695; FStar_Extraction_ML_Syntax.loc = _79_693}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_706; FStar_Extraction_ML_Syntax.loc = _79_704})::[]) when (is_machine_int m) -> begin
(let _170_563 = (let _170_562 = (FStar_Util.must (mk_width m))
in (_170_562, c))
in EConstant (_170_563))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _79_719; FStar_Extraction_ML_Syntax.loc = _79_717}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _170_565 = (let _170_564 = (translate_expr env arg)
in (_170_564, TInt (UInt64)))
in ECast (_170_565))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _170_567 = (let _170_566 = (translate_expr env arg)
in (_170_566, TInt (UInt32)))
in ECast (_170_567))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _170_569 = (let _170_568 = (translate_expr env arg)
in (_170_568, TInt (UInt32)))
in ECast (_170_569))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _170_571 = (let _170_570 = (translate_expr env arg)
in (_170_570, TInt (UInt32)))
in ECast (_170_571))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _170_573 = (let _170_572 = (translate_expr env arg)
in (_170_572, TInt (Int64)))
in ECast (_170_573))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _170_575 = (let _170_574 = (translate_expr env arg)
in (_170_574, TInt (Int32)))
in ECast (_170_575))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _170_577 = (let _170_576 = (translate_expr env arg)
in (_170_576, TInt (Int32)))
in ECast (_170_577))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _170_579 = (let _170_578 = (translate_expr env arg)
in (_170_578, TInt (Int32)))
in ECast (_170_579))
end else begin
(let _170_580 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _170_580))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _79_735; FStar_Extraction_ML_Syntax.loc = _79_733}, args) -> begin
(let _170_582 = (let _170_581 = (FStar_List.map (translate_expr env) args)
in (EQualified ((path, function_name)), _170_581))
in EApp (_170_582))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _79_747; FStar_Extraction_ML_Syntax.loc = _79_745}, t_from, t_to) -> begin
(let _170_585 = (let _170_584 = (translate_expr env e)
in (let _170_583 = (translate_type env t_to)
in (_170_584, _170_583)))
in ECast (_170_585))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_79_756) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (_79_759) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_79_762) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_79_765) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _170_586 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_170_586))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_79_770) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_773) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_79_776) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_79_779) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_79_782) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_79_785) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t branches -> (FStar_List.map (translate_branch env t) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t _79_795 -> (match (_79_795) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _79_798 = (translate_pat env t pat)
in (match (_79_798) with
| (env, pat) -> begin
(let _170_593 = (translate_expr env expr)
in (pat, _170_593))
end))
end else begin
(FStar_All.failwith "todo: translate_branch")
end
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  (env * pattern) = (fun env t p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
(env, PUnit)
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (b)) -> begin
(env, PBool (b))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name, _79_809) -> begin
(

let env = (extend env name false)
in (let _170_599 = (let _170_598 = (let _170_597 = (translate_type env t)
in {name = name; typ = _170_597; mut = false; mark = 0})
in PVar (_170_598))
in (env, _170_599)))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_79_815) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_79_818) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_79_821) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_79_824) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_79_827) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_79_832) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bool]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_79_836)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_79_841) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_79_844) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_79_847) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_79_850) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _170_606 = (let _170_605 = (FStar_List.map (translate_expr env) args)
in (EOp ((op, w)), _170_605))
in EApp (_170_606)))




