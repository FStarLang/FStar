
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
| EBufSub of (expr * expr)
| EMatch of (expr * branches)
| EOp of (op * width)
| ECast of (expr * typ) 
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
| TAlias of ident
| TBool 
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


let is_ECast = (fun _discr_ -> (match (_discr_) with
| ECast (_) -> begin
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


let is_TAlias = (fun _discr_ -> (match (_discr_) with
| TAlias (_) -> begin
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


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_79_9) -> begin
_79_9
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_79_12) -> begin
_79_12
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_79_15) -> begin
_79_15
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_79_18) -> begin
_79_18
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_79_21) -> begin
_79_21
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_79_24) -> begin
_79_24
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_79_27) -> begin
_79_27
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_79_30) -> begin
_79_30
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_79_33) -> begin
_79_33
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_79_36) -> begin
_79_36
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_79_39) -> begin
_79_39
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_79_42) -> begin
_79_42
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_79_45) -> begin
_79_45
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_79_48) -> begin
_79_48
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_79_51) -> begin
_79_51
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_79_54) -> begin
_79_54
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_79_57) -> begin
_79_57
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_79_60) -> begin
_79_60
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_79_63) -> begin
_79_63
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_79_66) -> begin
_79_66
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_79_70) -> begin
_79_70
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_79_73) -> begin
_79_73
end))


let ___TAlias____0 = (fun projectee -> (match (projectee) with
| TAlias (_79_76) -> begin
_79_76
end))


type version =
Prims.int


let current_version : version = 2


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _79_82 -> (match (_79_82) with
| (x, _79_79, _79_81) -> begin
x
end))


let snd3 = (fun _79_88 -> (match (_79_88) with
| (_79_84, x, _79_87) -> begin
x
end))


let thd3 = (fun _79_94 -> (match (_79_94) with
| (_79_90, _79_92, x) -> begin
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
| _79_105 -> begin
None
end))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))


type env =
{names : name Prims.list; module_name : Prims.string} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string  ->  env = (fun module_name -> {names = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _79_117 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _79_117.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _170_399 = (find_name env x)
in _170_399.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _79_133 -> begin
(let _170_407 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _170_407))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _79_146 -> (match (_79_146) with
| ((name, _79_142), _79_145) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _79_148 -> (match (_79_148) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> try
(match (()) with
| () -> begin
(let _170_441 = (translate_module m)
in Some (_170_441))
end)
with
| e when ((fst3 m) <> "Test") -> begin
(

let _79_154 = (let _170_443 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s\n%s\n" (fst3 m) _170_443))
in None)
end) modules)
end))
and translate_module : (Prims.string * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _79_162 -> (match (_79_162) with
| (module_name, modul, _79_161) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _79_168 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (module_name, program))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_198); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_79_188, _79_190, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _79_185; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _79_178; FStar_Extraction_ML_Syntax.loc = _79_176}; FStar_Extraction_ML_Syntax.print_typ = _79_174})::[]) -> begin
(

let _79_204 = ()
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _79_2 -> (match (_79_2) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_210, _79_212, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _170_449 = (find_return_type t)
in (translate_type env _170_449))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let body = (translate_expr env body)
in Some (DFunction ((t, name, binders, body))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_79_222) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Let]")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_79_225) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(let _170_452 = (let _170_451 = (let _170_450 = (translate_type env t)
in (name, _170_450))
in DTypeAlias (_170_451))
in Some (_170_452))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_79_236) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_79_239) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_79_242) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_79_250) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_253) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Fun]")
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
(let _170_455 = (translate_type env arg)
in TBuf (_170_455))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], ((module_name)::[], type_name)) when (module_name = env.module_name) -> begin
TAlias (type_name)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_308, p) -> begin
(let _170_456 = (FStar_Util.format1 "todo: translate_type [MLTY_Named] %s" (FStar_Extraction_ML_Syntax.string_of_mlpath p))
in (FStar_All.failwith _170_456))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_79_313) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _79_323 -> (match (_79_323) with
| ((name, _79_320), typ) -> begin
(let _170_461 = (translate_type env typ)
in {name = name; typ = _170_461; mut = false; mark = 0})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _79_332) -> begin
(let _170_464 = (find env name)
in EBound (_170_464))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_79_336) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Name]")
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_348); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _79_378 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _170_466 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.salloc") -> begin
t
end
| _79_362 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _170_465 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_79_368, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _79_366; FStar_Extraction_ML_Syntax.loc = _79_364} -> begin
body
end
| _79_375 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (_170_466, _170_465)))
end else begin
(typ, body)
end
in (match (_79_378) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _170_467 = (translate_type env typ)
in {name = name; typ = _170_467; mut = is_mut; mark = 0})
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
in (let _170_470 = (let _170_469 = (translate_expr env expr)
in (let _170_468 = (translate_branches env t branches)
in (_170_469, _170_468)))
in EMatch (_170_470)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_392; FStar_Extraction_ML_Syntax.loc = _79_390}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_402); FStar_Extraction_ML_Syntax.mlty = _79_399; FStar_Extraction_ML_Syntax.loc = _79_397})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _170_471 = (find env v)
in EBound (_170_471))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_412; FStar_Extraction_ML_Syntax.loc = _79_410}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_423); FStar_Extraction_ML_Syntax.mlty = _79_420; FStar_Extraction_ML_Syntax.loc = _79_418})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _170_475 = (let _170_474 = (let _170_472 = (find env v)
in EBound (_170_472))
in (let _170_473 = (translate_expr env e)
in (_170_474, _170_473)))
in EAssign (_170_475))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_433; FStar_Extraction_ML_Syntax.loc = _79_431}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") -> begin
(let _170_478 = (let _170_477 = (translate_expr env e1)
in (let _170_476 = (translate_expr env e2)
in (_170_477, _170_476)))
in EBufRead (_170_478))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_445; FStar_Extraction_ML_Syntax.loc = _79_443}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _170_481 = (let _170_480 = (translate_expr env e1)
in (let _170_479 = (translate_expr env e2)
in (_170_480, _170_479)))
in EBufCreate (_170_481))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_457; FStar_Extraction_ML_Syntax.loc = _79_455}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") -> begin
(let _170_485 = (let _170_484 = (translate_expr env e1)
in (let _170_483 = (translate_expr env e2)
in (let _170_482 = (translate_expr env e3)
in (_170_484, _170_483, _170_482))))
in EBufWrite (_170_485))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Plus_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_470; FStar_Extraction_ML_Syntax.loc = _79_468}, args) when (is_machine_int m) -> begin
(let _170_486 = (FStar_Util.must (mk_width m))
in (mk_op env _170_486 Add args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Plus_Percent_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_484; FStar_Extraction_ML_Syntax.loc = _79_482}, args) when (is_machine_int m) -> begin
(let _170_487 = (FStar_Util.must (mk_width m))
in (mk_op env _170_487 AddW args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Subtraction_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_498; FStar_Extraction_ML_Syntax.loc = _79_496}, args) when (is_machine_int m) -> begin
(let _170_488 = (FStar_Util.must (mk_width m))
in (mk_op env _170_488 Sub args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Subtraction_Percent_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_512; FStar_Extraction_ML_Syntax.loc = _79_510}, args) when (is_machine_int m) -> begin
(let _170_489 = (FStar_Util.must (mk_width m))
in (mk_op env _170_489 SubW args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Star_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_526; FStar_Extraction_ML_Syntax.loc = _79_524}, args) when (is_machine_int m) -> begin
(let _170_490 = (FStar_Util.must (mk_width m))
in (mk_op env _170_490 Mult args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Bar_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_540; FStar_Extraction_ML_Syntax.loc = _79_538}, args) when (is_machine_int m) -> begin
(let _170_491 = (FStar_Util.must (mk_width m))
in (mk_op env _170_491 BOr args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Hat_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_554; FStar_Extraction_ML_Syntax.loc = _79_552}, args) when (is_machine_int m) -> begin
(let _170_492 = (FStar_Util.must (mk_width m))
in (mk_op env _170_492 BXor args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Amp_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_568; FStar_Extraction_ML_Syntax.loc = _79_566}, args) when (is_machine_int m) -> begin
(let _170_493 = (FStar_Util.must (mk_width m))
in (mk_op env _170_493 BAnd args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Greater_Greater_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_582; FStar_Extraction_ML_Syntax.loc = _79_580}, args) when (is_machine_int m) -> begin
(let _170_494 = (FStar_Util.must (mk_width m))
in (mk_op env _170_494 BShiftR args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Less_Less_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_596; FStar_Extraction_ML_Syntax.loc = _79_594}, args) when (is_machine_int m) -> begin
(let _170_495 = (FStar_Util.must (mk_width m))
in (mk_op env _170_495 BShiftL args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Equals_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_610; FStar_Extraction_ML_Syntax.loc = _79_608}, args) when (is_machine_int m) -> begin
(let _170_496 = (FStar_Util.must (mk_width m))
in (mk_op env _170_496 Eq args))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_624; FStar_Extraction_ML_Syntax.loc = _79_622}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_631; FStar_Extraction_ML_Syntax.loc = _79_629})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt8.uint_to_t") -> begin
EConstant ((UInt8, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_644; FStar_Extraction_ML_Syntax.loc = _79_642}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_651; FStar_Extraction_ML_Syntax.loc = _79_649})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt16.uint_to_t") -> begin
EConstant ((UInt16, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_664; FStar_Extraction_ML_Syntax.loc = _79_662}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_671; FStar_Extraction_ML_Syntax.loc = _79_669})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt32.uint_to_t") -> begin
EConstant ((UInt32, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_684; FStar_Extraction_ML_Syntax.loc = _79_682}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_691; FStar_Extraction_ML_Syntax.loc = _79_689})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt64.uint_to_t") -> begin
EConstant ((UInt64, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_704; FStar_Extraction_ML_Syntax.loc = _79_702}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_711; FStar_Extraction_ML_Syntax.loc = _79_709})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int8.uint_to_t") -> begin
EConstant ((Int8, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_724; FStar_Extraction_ML_Syntax.loc = _79_722}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_731; FStar_Extraction_ML_Syntax.loc = _79_729})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int16.uint_to_t") -> begin
EConstant ((Int16, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_744; FStar_Extraction_ML_Syntax.loc = _79_742}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_751; FStar_Extraction_ML_Syntax.loc = _79_749})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int32.uint_to_t") -> begin
EConstant ((Int32, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_764; FStar_Extraction_ML_Syntax.loc = _79_762}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_771; FStar_Extraction_ML_Syntax.loc = _79_769})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int64.uint_to_t") -> begin
EConstant ((Int64, c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name ((module_name)::[], function_name); FStar_Extraction_ML_Syntax.mlty = _79_784; FStar_Extraction_ML_Syntax.loc = _79_782}, args) when (module_name = env.module_name) -> begin
(let _170_498 = (let _170_497 = (FStar_List.map (translate_expr env) args)
in (EQualified (([], function_name)), _170_497))
in EApp (_170_498))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _79_797; FStar_Extraction_ML_Syntax.loc = _79_795}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _170_500 = (let _170_499 = (translate_expr env arg)
in (_170_499, TInt (UInt64)))
in ECast (_170_500))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _170_502 = (let _170_501 = (translate_expr env arg)
in (_170_501, TInt (UInt32)))
in ECast (_170_502))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _170_504 = (let _170_503 = (translate_expr env arg)
in (_170_503, TInt (UInt32)))
in ECast (_170_504))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _170_506 = (let _170_505 = (translate_expr env arg)
in (_170_505, TInt (UInt32)))
in ECast (_170_506))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _170_508 = (let _170_507 = (translate_expr env arg)
in (_170_507, TInt (Int64)))
in ECast (_170_508))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _170_510 = (let _170_509 = (translate_expr env arg)
in (_170_509, TInt (Int32)))
in ECast (_170_510))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _170_512 = (let _170_511 = (translate_expr env arg)
in (_170_511, TInt (Int32)))
in ECast (_170_512))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _170_514 = (let _170_513 = (translate_expr env arg)
in (_170_513, TInt (Int32)))
in ECast (_170_514))
end else begin
(let _170_515 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _170_515))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_813; FStar_Extraction_ML_Syntax.loc = _79_811}, args) -> begin
(let _170_517 = (let _170_516 = (FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "todo: translate_expr [MLE_App=%s; %s]" (FStar_Extraction_ML_Syntax.string_of_mlpath p) _170_516))
in (FStar_All.failwith _170_517))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_79_821) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (_79_824) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_79_827) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_79_830) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_79_833) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _170_518 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_170_518))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_79_838) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_841) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_79_844) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_79_847) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_79_850) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_79_853) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t branches -> (FStar_List.map (translate_branch env t) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t _79_863 -> (match (_79_863) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _79_866 = (translate_pat env t pat)
in (match (_79_866) with
| (env, pat) -> begin
(let _170_525 = (translate_expr env expr)
in (pat, _170_525))
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
| FStar_Extraction_ML_Syntax.MLP_Var (name, _79_877) -> begin
(

let env = (extend env name false)
in (let _170_531 = (let _170_530 = (let _170_529 = (translate_type env t)
in {name = name; typ = _170_529; mut = false; mark = 0})
in PVar (_170_530))
in (env, _170_531)))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_79_883) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_79_886) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_79_889) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_79_892) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_79_895) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_79_900) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bool]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_79_904)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_79_909) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_79_912) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_79_915) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_79_918) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end))
and mk_op : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _170_538 = (let _170_537 = (FStar_List.map (translate_expr env) args)
in (EOp ((op, w)), _170_537))
in EApp (_170_538)))




