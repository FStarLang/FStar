
open Prims

type decl =
| DFunction of (typ * ident * binder Prims.list * expr) 
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
| Sub
| Div
| Mult
| Mod 
 and pattern =
| PUnit 
 and constant =
| CInt of Prims.string 
 and binder =
{name : ident; typ : typ; mut : Prims.bool} 
 and typ =
| TInt32
| TBuf of typ
| TUnit 
 and program =
decl Prims.list 
 and branches =
branch Prims.list 
 and branch =
(pattern * expr) 
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


let is_PUnit = (fun _discr_ -> (match (_discr_) with
| PUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_CInt = (fun _discr_ -> (match (_discr_) with
| CInt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))


let is_TInt32 = (fun _discr_ -> (match (_discr_) with
| TInt32 (_) -> begin
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


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_79_5) -> begin
_79_5
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_79_8) -> begin
_79_8
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_79_11) -> begin
_79_11
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_79_14) -> begin
_79_14
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_79_17) -> begin
_79_17
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_79_20) -> begin
_79_20
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_79_23) -> begin
_79_23
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_79_26) -> begin
_79_26
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_79_29) -> begin
_79_29
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_79_32) -> begin
_79_32
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_79_35) -> begin
_79_35
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_79_38) -> begin
_79_38
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_79_41) -> begin
_79_41
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_79_44) -> begin
_79_44
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_79_47) -> begin
_79_47
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_79_50) -> begin
_79_50
end))


let ___CInt____0 = (fun projectee -> (match (projectee) with
| CInt (_79_52) -> begin
_79_52
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_79_56) -> begin
_79_56
end))


type version =
Prims.int


let current_version : version = 1


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _79_62 -> (match (_79_62) with
| (x, _79_59, _79_61) -> begin
x
end))


let snd3 = (fun _79_68 -> (match (_79_68) with
| (_79_64, x, _79_67) -> begin
x
end))


let thd3 = (fun _79_74 -> (match (_79_74) with
| (_79_70, _79_72, x) -> begin
x
end))


type env =
{names : name Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : env = {names = []}


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _79_83 = env
in {names = ({pretty = x; mut = is_mut})::env.names}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _169_285 = (find_name env x)
in _169_285.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> (FStar_List.index (fun name -> (name.pretty = x)) env.names))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _79_97 -> (match (_79_97) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> try
(match (()) with
| () -> begin
(let _169_313 = (translate_module m)
in Some (_169_313))
end)
with
| e -> begin
(

let _79_103 = (let _169_315 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s\n%s\n" (fst3 m) _169_315))
in None)
end) modules)
end))
and translate_module : (Prims.string * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _79_111 -> (match (_79_111) with
| (name, modul, _79_110) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl empty) decls)
end
| _79_117 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (name, program))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, {FStar_Extraction_ML_Syntax.mllb_name = (name, _79_147); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_79_137, _79_139, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _79_134; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _79_127; FStar_Extraction_ML_Syntax.loc = _79_125}; FStar_Extraction_ML_Syntax.print_typ = _79_123}::[]) -> begin
(

let _79_153 = ()
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let t = (translate_type env t)
in (

let binders = (translate_binders env args)
in (

let body = (translate_expr env body)
in Some (DFunction ((t, name, binders, body))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_79_160) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Let]")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_79_163) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_79_166) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_79_169) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_79_172) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_79_180) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_183) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Fun]")
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_186, p) -> begin
(match ((FStar_Extraction_ML_Syntax.string_of_mlpath p)) with
| "Prims.unit" -> begin
TUnit
end
| "Prims.int" -> begin
TInt32
end
| _79_193 -> begin
(let _169_321 = (FStar_Util.format1 "todo: translate_type [MLTY_Named] %s" (FStar_Extraction_ML_Syntax.string_of_mlpath p))
in (FStar_All.failwith _169_321))
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_79_195) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _79_205 -> (match (_79_205) with
| ((name, _79_202), typ) -> begin
(let _169_326 = (translate_type env typ)
in {name = name; typ = _169_326; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _79_214) -> begin
(let _169_329 = (find env name)
in EBound (_169_329))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_79_218) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Name]")
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, {FStar_Extraction_ML_Syntax.mllb_name = (name, _79_230); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print}::[]), continuation) -> begin
(

let _79_260 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _169_331 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named (t::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.ref") -> begin
t
end
| _79_244 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _169_330 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_79_250, body::[]); FStar_Extraction_ML_Syntax.mlty = _79_248; FStar_Extraction_ML_Syntax.loc = _79_246} -> begin
body
end
| _79_257 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (_169_331, _169_330)))
end else begin
(typ, body)
end
in (match (_79_260) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _169_332 = (translate_type env typ)
in {name = name; typ = _169_332; mut = is_mut})
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
(let _169_335 = (let _169_334 = (translate_expr env expr)
in (let _169_333 = (translate_branches env branches)
in (_169_334, _169_333)))
in EMatch (_169_335))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_273; FStar_Extraction_ML_Syntax.loc = _79_271}, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_283); FStar_Extraction_ML_Syntax.mlty = _79_280; FStar_Extraction_ML_Syntax.loc = _79_278}::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.read") && (is_mutable env v)) -> begin
(let _169_336 = (find env v)
in EBound (_169_336))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_293; FStar_Extraction_ML_Syntax.loc = _79_291}, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_304); FStar_Extraction_ML_Syntax.mlty = _79_301; FStar_Extraction_ML_Syntax.loc = _79_299}::e::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.write") && (is_mutable env v)) -> begin
(let _169_340 = (let _169_339 = (let _169_337 = (find env v)
in EBound (_169_337))
in (let _169_338 = (translate_expr env e)
in (_169_339, _169_338)))
in EAssign (_169_340))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_314; FStar_Extraction_ML_Syntax.loc = _79_312}, args) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.op_Addition") -> begin
(let _169_342 = (let _169_341 = (FStar_List.map (translate_expr env) args)
in (EOp (Add), _169_341))
in EApp (_169_342))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_324; FStar_Extraction_ML_Syntax.loc = _79_322}, _79_329) -> begin
(let _169_343 = (FStar_Util.format1 "todo: translate_expr [MLE_App=%s]" (FStar_Extraction_ML_Syntax.string_of_mlpath p))
in (FStar_All.failwith _169_343))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_79_333) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (_79_336) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_79_339) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_79_342) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_79_345) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _169_344 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_169_344))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_79_350) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_353) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_79_356) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_79_359) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_79_362) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_79_365) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _79_373 -> (match (_79_373) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(let _169_350 = (translate_pat env pat)
in (let _169_349 = (translate_expr env expr)
in (_169_350, _169_349)))
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
| FStar_Extraction_ML_Syntax.MLP_Const (_79_380) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Var (_79_383) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Var]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_79_386) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_79_389) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_79_392) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_79_395) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_79_400) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bool]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, _79_404) -> begin
EConstant (CInt (s))
end
| FStar_Extraction_ML_Syntax.MLC_Float (_79_408) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_79_411) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_79_414) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_79_417) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end))




