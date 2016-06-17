
open Prims

type decl =
| DFunction of (typ * ident * binder Prims.list * expr)
| DTypeAlias of (ident * typ) 
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
| EBufSub of (expr * expr * expr)
| EMatch of (expr * branches)
| EOp of op 
 and op =
| Add
| AddW
| Sub
| Div
| Mult
| Mod
| Or
| And
| Xor
| ShiftL
| ShiftR 
 and pattern =
| PUnit 
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
{name : ident; typ : typ; mut : Prims.bool} 
 and typ =
| TInt of width
| TBuf of typ
| TUnit
| TAlias of ident 
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


let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
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


let is_Xor = (fun _discr_ -> (match (_discr_) with
| Xor (_) -> begin
true
end
| _ -> begin
false
end))


let is_ShiftL = (fun _discr_ -> (match (_discr_) with
| ShiftL (_) -> begin
true
end
| _ -> begin
false
end))


let is_ShiftR = (fun _discr_ -> (match (_discr_) with
| ShiftR (_) -> begin
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


let is_TAlias = (fun _discr_ -> (match (_discr_) with
| TAlias (_) -> begin
true
end
| _ -> begin
false
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_79_8) -> begin
_79_8
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_79_11) -> begin
_79_11
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_79_14) -> begin
_79_14
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_79_17) -> begin
_79_17
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_79_20) -> begin
_79_20
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_79_23) -> begin
_79_23
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_79_26) -> begin
_79_26
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_79_29) -> begin
_79_29
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_79_32) -> begin
_79_32
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_79_35) -> begin
_79_35
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_79_38) -> begin
_79_38
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_79_41) -> begin
_79_41
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_79_44) -> begin
_79_44
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_79_47) -> begin
_79_47
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_79_50) -> begin
_79_50
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_79_53) -> begin
_79_53
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_79_56) -> begin
_79_56
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_79_60) -> begin
_79_60
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_79_63) -> begin
_79_63
end))


let ___TAlias____0 = (fun projectee -> (match (projectee) with
| TAlias (_79_66) -> begin
_79_66
end))


type version =
Prims.int


let current_version : version = 1


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _79_72 -> (match (_79_72) with
| (x, _79_69, _79_71) -> begin
x
end))


let snd3 = (fun _79_78 -> (match (_79_78) with
| (_79_74, x, _79_77) -> begin
x
end))


let thd3 = (fun _79_84 -> (match (_79_84) with
| (_79_80, _79_82, x) -> begin
x
end))


let is_machine_int : Prims.string  ->  Prims.bool = (fun _79_1 -> (match (_79_1) with
| ("UInt8") | ("UInt16") | ("UInt32") | ("UInt64") | ("Int8") | ("Int16") | ("Int32") | ("Int64") -> begin
true
end
| _79_95 -> begin
false
end))


type env =
{names : name Prims.list; module_name : Prims.string} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string  ->  env = (fun module_name -> {names = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _79_106 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _79_106.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _170_349 = (find_name env x)
in _170_349.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _79_122 -> begin
(let _170_357 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _170_357))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _79_135 -> (match (_79_135) with
| ((name, _79_131), _79_134) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _79_137 -> (match (_79_137) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> try
(match (()) with
| () -> begin
(let _170_387 = (translate_module m)
in Some (_170_387))
end)
with
| e when ((fst3 m) <> "Test") -> begin
(

let _79_143 = (let _170_389 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s\n%s\n" (fst3 m) _170_389))
in None)
end) modules)
end))
and translate_module : (Prims.string * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _79_151 -> (match (_79_151) with
| (module_name, modul, _79_150) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _79_157 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (module_name, program))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_187); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_79_177, _79_179, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _79_174; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _79_167; FStar_Extraction_ML_Syntax.loc = _79_165}; FStar_Extraction_ML_Syntax.print_typ = _79_163})::[]) -> begin
(

let _79_193 = ()
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _79_2 -> (match (_79_2) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_199, _79_201, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _170_395 = (find_return_type t)
in (translate_type env _170_395))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let body = (translate_expr env body)
in Some (DFunction ((t, name, binders, body))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_79_211) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Let]")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_79_214) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(let _170_398 = (let _170_397 = (let _170_396 = (translate_type env t)
in (name, _170_396))
in DTypeAlias (_170_397))
in Some (_170_398))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_79_225) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_79_228) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_79_231) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_79_239) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_242) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Fun]")
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
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
(let _170_401 = (translate_type env arg)
in TBuf (_170_401))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], ((module_name)::[], type_name)) when (module_name = env.module_name) -> begin
TAlias (type_name)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_293, p) -> begin
(let _170_402 = (FStar_Util.format1 "todo: translate_type [MLTY_Named] %s" (FStar_Extraction_ML_Syntax.string_of_mlpath p))
in (FStar_All.failwith _170_402))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_79_298) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _79_308 -> (match (_79_308) with
| ((name, _79_305), typ) -> begin
(let _170_407 = (translate_type env typ)
in {name = name; typ = _170_407; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _79_317) -> begin
(let _170_410 = (find env name)
in EBound (_170_410))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_79_321) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Name]")
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_333); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _79_363 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _170_412 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.salloc") -> begin
t
end
| _79_347 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _170_411 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_79_353, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _79_351; FStar_Extraction_ML_Syntax.loc = _79_349} -> begin
body
end
| _79_360 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (_170_412, _170_411)))
end else begin
(typ, body)
end
in (match (_79_363) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _170_413 = (translate_type env typ)
in {name = name; typ = _170_413; mut = is_mut})
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
(let _170_416 = (let _170_415 = (translate_expr env expr)
in (let _170_414 = (translate_branches env branches)
in (_170_415, _170_414)))
in EMatch (_170_416))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_376; FStar_Extraction_ML_Syntax.loc = _79_374}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_386); FStar_Extraction_ML_Syntax.mlty = _79_383; FStar_Extraction_ML_Syntax.loc = _79_381})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _170_417 = (find env v)
in EBound (_170_417))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_396; FStar_Extraction_ML_Syntax.loc = _79_394}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_407); FStar_Extraction_ML_Syntax.mlty = _79_404; FStar_Extraction_ML_Syntax.loc = _79_402})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _170_421 = (let _170_420 = (let _170_418 = (find env v)
in EBound (_170_418))
in (let _170_419 = (translate_expr env e)
in (_170_420, _170_419)))
in EAssign (_170_421))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_417; FStar_Extraction_ML_Syntax.loc = _79_415}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") -> begin
(let _170_424 = (let _170_423 = (translate_expr env e1)
in (let _170_422 = (translate_expr env e2)
in (_170_423, _170_422)))
in EBufRead (_170_424))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_429; FStar_Extraction_ML_Syntax.loc = _79_427}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _170_427 = (let _170_426 = (translate_expr env e1)
in (let _170_425 = (translate_expr env e2)
in (_170_426, _170_425)))
in EBufCreate (_170_427))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_441; FStar_Extraction_ML_Syntax.loc = _79_439}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") -> begin
(let _170_431 = (let _170_430 = (translate_expr env e1)
in (let _170_429 = (translate_expr env e2)
in (let _170_428 = (translate_expr env e3)
in (_170_430, _170_429, _170_428))))
in EBufWrite (_170_431))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Plus_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_454; FStar_Extraction_ML_Syntax.loc = _79_452}, args) when (is_machine_int m) -> begin
(mk_op env Add args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Plus_Percent_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_468; FStar_Extraction_ML_Syntax.loc = _79_466}, args) when (is_machine_int m) -> begin
(mk_op env AddW args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Subtraction_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_482; FStar_Extraction_ML_Syntax.loc = _79_480}, args) when (is_machine_int m) -> begin
(mk_op env Sub args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Bar_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_496; FStar_Extraction_ML_Syntax.loc = _79_494}, args) when (is_machine_int m) -> begin
(mk_op env Or args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Hat_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_510; FStar_Extraction_ML_Syntax.loc = _79_508}, args) when (is_machine_int m) -> begin
(mk_op env Xor args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Amp_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_524; FStar_Extraction_ML_Syntax.loc = _79_522}, args) when (is_machine_int m) -> begin
(mk_op env And args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Greater_Greater_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_538; FStar_Extraction_ML_Syntax.loc = _79_536}, args) when (is_machine_int m) -> begin
(mk_op env ShiftR args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Less_Less_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_552; FStar_Extraction_ML_Syntax.loc = _79_550}, args) when (is_machine_int m) -> begin
(mk_op env ShiftL args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_566; FStar_Extraction_ML_Syntax.loc = _79_564}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_573; FStar_Extraction_ML_Syntax.loc = _79_571})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt8.uint_to_t") -> begin
EConstant ((UInt8, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_586; FStar_Extraction_ML_Syntax.loc = _79_584}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_593; FStar_Extraction_ML_Syntax.loc = _79_591})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt16.uint_to_t") -> begin
EConstant ((UInt16, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_606; FStar_Extraction_ML_Syntax.loc = _79_604}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_613; FStar_Extraction_ML_Syntax.loc = _79_611})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt32.uint_to_t") -> begin
EConstant ((UInt32, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_626; FStar_Extraction_ML_Syntax.loc = _79_624}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_633; FStar_Extraction_ML_Syntax.loc = _79_631})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt64.uint_to_t") -> begin
EConstant ((UInt64, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_646; FStar_Extraction_ML_Syntax.loc = _79_644}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_653; FStar_Extraction_ML_Syntax.loc = _79_651})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int8.uint_to_t") -> begin
EConstant ((Int8, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_666; FStar_Extraction_ML_Syntax.loc = _79_664}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_673; FStar_Extraction_ML_Syntax.loc = _79_671})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int16.uint_to_t") -> begin
EConstant ((Int16, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_686; FStar_Extraction_ML_Syntax.loc = _79_684}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_693; FStar_Extraction_ML_Syntax.loc = _79_691})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int32.uint_to_t") -> begin
EConstant ((Int32, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_706; FStar_Extraction_ML_Syntax.loc = _79_704}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_713; FStar_Extraction_ML_Syntax.loc = _79_711})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int64.uint_to_t") -> begin
EConstant ((Int64, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name ((module_name)::[], function_name); FStar_Extraction_ML_Syntax.mlty = _79_726; FStar_Extraction_ML_Syntax.loc = _79_724}, args) when (module_name = env.module_name) -> begin
(let _170_433 = (let _170_432 = (FStar_List.map (translate_expr env) args)
in (EQualified (([], function_name)), _170_432))
in EApp (_170_433))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_739; FStar_Extraction_ML_Syntax.loc = _79_737}, args) -> begin
(let _170_435 = (let _170_434 = (FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "todo: translate_expr [MLE_App=%s; %s]" (FStar_Extraction_ML_Syntax.string_of_mlpath p) _170_434))
in (FStar_All.failwith _170_435))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_79_747) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (_79_750) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_79_753) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_79_756) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_79_759) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _170_436 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_170_436))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_79_764) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_767) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_79_770) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_79_773) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_79_776) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_79_779) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _79_787 -> (match (_79_787) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(let _170_442 = (translate_pat env pat)
in (let _170_441 = (translate_expr env expr)
in (_170_442, _170_441)))
end else begin
(FStar_All.failwith "todo: translate_branch")
end
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  pattern = (fun env p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
PUnit
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_79_794) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Var (_79_797) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Var]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_79_800) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_79_803) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_79_806) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_79_809) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_79_814) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bool]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_79_818)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_79_823) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_79_826) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_79_829) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_79_832) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end))
and mk_op : env  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env op args -> (let _170_450 = (let _170_449 = (FStar_List.map (translate_expr env) args)
in (EOp (op), _170_449))
in EApp (_170_450)))




