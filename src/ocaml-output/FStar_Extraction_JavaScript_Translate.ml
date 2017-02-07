
open Prims

type file =
(Prims.string * FStar_Extraction_JavaScript_Ast.t)

type env =
{names : name Prims.list; module_name : Prims.string; export_module_names : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let empty : Prims.string  ->  env = (fun module_name -> {names = []; module_name = module_name; export_module_names = []})


let mk_op_bin : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_bin Prims.option = (fun uu___137_50 -> (match (uu___137_50) with
| "op_Addition" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Plus)
end
| "op_Subtraction" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Minus)
end
| "op_Multiply" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Mult)
end
| "op_Division" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Div)
end
| "op_Equality" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Equal)
end
| "op_disEquality" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_NotEqual)
end
| "op_LessThanOrEqual" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_LessThanEqual)
end
| "op_GreaterThanOrEqual" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_GreaterThanEqual)
end
| "op_LessThan" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_LessThan)
end
| "op_GreaterThan" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_GreaterThan)
end
| "op_Modulus" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSB_Mod)
end
| uu____52 -> begin
None
end))


let is_op_bin : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bin op) <> None))


let mk_op_un : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_un Prims.option = (fun uu___138_60 -> (match (uu___138_60) with
| "op_Negation" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSU_Not)
end
| "op_Minus" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSU_Minus)
end
| uu____62 -> begin
None
end))


let is_op_un : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_un op) <> None))


let mk_op_bool : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_log Prims.option = (fun uu___139_70 -> (match (uu___139_70) with
| "op_AmpAmp" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_And)
end
| "op_BarBar" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_Or)
end
| uu____72 -> begin
None
end))


let is_op_bool : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bool op) <> None))


let mk_standart_type : Prims.string  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option = (fun uu___140_80 -> (match (uu___140_80) with
| "unit" -> begin
Some (FStar_Extraction_JavaScript_Ast.JST_Null)
end
| "bool" -> begin
Some (FStar_Extraction_JavaScript_Ast.JST_Boolean)
end
| ("int") | ("nat") -> begin
Some (FStar_Extraction_JavaScript_Ast.JST_Number)
end
| "string" -> begin
Some (FStar_Extraction_JavaScript_Ast.JST_String)
end
| uu____82 -> begin
None
end))


let is_standart_type : Prims.string  ->  Prims.bool = (fun t -> ((mk_standart_type t) <> None))


let float_of_int : Prims.int  ->  FStar_BaseTypes.float = (fun i -> (FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)))


let isMutable = (fun typ -> (match (typ) with
| None -> begin
false
end
| Some (uu____105, ty) -> begin
(match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____109, p) when (let _0_374 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_374 = "FStar.ST.ref")) -> begin
true
end
| uu____113 -> begin
false
end)
end))


let extendEnv = (fun env uu____135 typ -> (match (uu____135) with
| (path, n) -> begin
(

let path = (FStar_String.concat "_" path)
in (match (((path = env.module_name) || (path = ""))) with
| true -> begin
(

let uu___141_148 = env
in {names = ({pretty = n; mut = (isMutable typ)})::env.names; module_name = uu___141_148.module_name; export_module_names = uu___141_148.export_module_names})
end
| uu____149 -> begin
(

let n = (Prims.strcat path (Prims.strcat "." n))
in (match ((not ((FStar_List.existsb (fun x -> (x = path)) env.export_module_names)))) with
| true -> begin
(

let uu___142_152 = env
in {names = ({pretty = n; mut = (isMutable typ)})::env.names; module_name = uu___142_152.module_name; export_module_names = (path)::env.export_module_names})
end
| uu____153 -> begin
(

let uu___143_154 = env
in {names = ({pretty = n; mut = (isMutable typ)})::env.names; module_name = uu___143_154.module_name; export_module_names = uu___143_154.export_module_names})
end))
end))
end))


let findEnv : env  ->  Prims.string  ->  Prims.int = (fun env name -> (FStar_List.index (fun x -> (x.pretty = name)) env.names))


let isInEnv : env  ->  Prims.string  ->  Prims.bool = (fun env name -> (FStar_List.existsb (fun x -> (x.pretty = name)) env.names))


let rec is_pure_expr = (fun e var -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (n, uu____188) -> begin
(n <> (Prims.fst var))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, uu____190) -> begin
(is_pure_expr expr var)
end
| FStar_Extraction_ML_Syntax.MLE_CTor (p, le) -> begin
(not ((let _0_375 = (FStar_List.map (fun x -> (is_pure_expr x var)) le)
in (FStar_List.contains false _0_375))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (le) -> begin
(not ((let _0_376 = (FStar_List.map (fun x -> (is_pure_expr x var)) le)
in (FStar_List.contains false _0_376))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____199, lne) -> begin
(not ((let _0_377 = (FStar_List.map (fun uu____211 -> (match (uu____211) with
| (n, e) -> begin
(is_pure_expr e var)
end)) lne)
in (FStar_List.contains false _0_377))))
end
| FStar_Extraction_ML_Syntax.MLE_App (uu____216, args) -> begin
(not ((let _0_378 = (FStar_List.map (fun x -> (is_pure_expr x var)) args)
in (FStar_List.contains false _0_378))))
end
| uu____221 -> begin
false
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____335 -> (match (uu____335) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____366 = m
in (match (uu____366) with
| ((prefix, final), uu____378, uu____379) -> begin
(FStar_String.concat "_" (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
((FStar_Util.print1 "Attempting to translate module %s\n" m_name);
Some ((translate_module (empty m_name) m));
)
end)
with
| e -> begin
((let _0_379 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _0_379));
None;
)
end)) modules)
end))
and translate_module : env  ->  ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun env uu____400 -> (match (uu____400) with
| (module_name, modul, uu____412) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let update_env = (fun uu____435 -> (

let uu___146_436 = env
in {names = []; module_name = uu___146_436.module_name; export_module_names = uu___146_436.export_module_names}))
in (

let res = (FStar_List.filter_map (translate_decl (update_env ())) decls)
in (

let create_module_imports = (let _0_383 = (let _0_381 = (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (((m), (None)))) env.export_module_names)
in (FStar_All.pipe_right _0_381 (fun _0_380 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_0_380))))
in (FStar_All.pipe_right _0_383 (fun _0_382 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_0_382))))
in (FStar_List.append ((create_module_imports)::[]) res))))
end
| uu____443 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in ((env.module_name), (program)))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (uu____453, c_flag, lfunc) -> begin
(

let for1 = (fun uu____462 -> (match (uu____462) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, uu____465); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = (match (((not (pt)) || unit_b)) with
| true -> begin
None
end
| uu____474 -> begin
(match (tys) with
| None -> begin
None
end
| Some (lp, ty) -> begin
(

let lp_generic = (match (lp) with
| [] -> begin
None
end
| uu____486 -> begin
Some ((FStar_List.map (fun uu____490 -> (match (uu____490) with
| (id, uu____494) -> begin
id
end)) lp))
end)
in (let _0_385 = (translate_type ty lp_generic env)
in (FStar_All.pipe_right _0_385 (fun _0_384 -> Some (_0_384)))))
end)
end)
in (

let is_private = (FStar_List.contains FStar_Extraction_ML_Syntax.Private c_flag)
in (

let env = (extendEnv env (([]), (name)) tys)
in (

let c = (

let uu____501 = (is_pure_expr expr ((name), (None)))
in (match (uu____501) with
| true -> begin
(

let var_decl_q = (match ((isMutable tys)) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JSV_Let
end
| uu____506 -> begin
FStar_Extraction_JavaScript_Ast.JSV_Const
end)
in (let _0_388 = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((let _0_387 = (let _0_386 = Some ((translate_expr_pure expr env))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (_0_386)))
in ((_0_387), (var_decl_q))))
in (_0_388)::[]))
end
| uu____512 -> begin
(translate_expr expr ((name), (t)) [] env false)
end))
in (match (is_private) with
| true -> begin
c
end
| uu____515 -> begin
(FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (FStar_Extraction_JavaScript_Ast.JSS_Block (c))), (FStar_Extraction_JavaScript_Ast.ExportValue))))::[]
end)))))
end))
in (let _0_394 = (let _0_392 = (let _0_390 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _0_390 (fun _0_389 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_0_389))))
in (FStar_All.pipe_right _0_392 (fun _0_391 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_0_391))))
in (FStar_All.pipe_right _0_394 (fun _0_393 -> Some (_0_393)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____518) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____519, name, uu____521, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| uu____548 -> begin
Some ((FStar_List.map (fun uu____552 -> (match (uu____552) with
| (id, uu____556) -> begin
id
end)) tparams))
end)
in (

let forbody = (fun body -> (

let get_export = (fun stmt -> FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (stmt)), (FStar_Extraction_JavaScript_Ast.ExportType))))
in (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((let _0_395 = (translate_type t tparams env)
in ((((name), (None))), (tparams), (_0_395))))))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun uu____593 -> (match (uu____593) with
| (n, t) -> begin
(let _0_396 = (translate_type t tparams env)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_0_396)))
end)) fields)
in (get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((FStar_List.append tag fields_t)))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.mapi (fun i t -> (let _0_400 = FStar_Extraction_JavaScript_Ast.JSO_Identifier ((let _0_398 = (let _0_397 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_397))
in ((_0_398), (None))))
in (let _0_399 = (translate_type t tparams env)
in ((_0_400), (_0_399))))) fields))
in (

let lfields_t = (FStar_List.map (fun uu____645 -> (match (uu____645) with
| (n, l) -> begin
(get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((let _0_402 = FStar_Extraction_JavaScript_Ast.JST_Object ((let _0_401 = (fields_t l)
in (FStar_List.append (tag n) _0_401)))
in ((((n), (None))), (tparams), (_0_402))))))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _0_404 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((x), (None)))) t)
in (FStar_All.pipe_right _0_404 (fun _0_403 -> Some (_0_403))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun uu____684 -> (match (uu____684) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((n), (tparams_gen)))
end)) lfields)
in (

let union_t = (get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Union (lnames))))))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append lfields_t ((union_t)::[])))))))))
end)))
in (

let body_t = (match (body) with
| None -> begin
(failwith "todo: translate_decl [MLM_Ty] with empty body")
end
| Some (v) -> begin
(forbody v)
end)
in (let _0_407 = (FStar_All.pipe_right body_t (fun _0_405 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_0_405)))
in (FStar_All.pipe_right _0_407 (fun _0_406 -> Some (_0_406)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (uu____704) -> begin
(failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____706) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _0_410 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block ([])) (fun _0_408 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_0_408)))
in (FStar_All.pipe_right _0_410 (fun _0_409 -> Some (_0_409))))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____711) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  env  ->  Prims.bool  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.list = (fun e var lstmt env isDecl -> (

let get_res = (fun expr new_fv -> (

let expr = (match (expr) with
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (uu____739) -> begin
(match (isDecl) with
| true -> begin
(FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_Expression (expr))::(FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))))))::[]) lstmt)
end
| uu____743 -> begin
(FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_Expression (expr))::(FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) lstmt)
end)
end
| uu____748 -> begin
(match (isDecl) with
| true -> begin
(FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (expr)))))::[]) lstmt)
end
| uu____750 -> begin
(FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (expr)))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) lstmt)
end)
end)
in (match (new_fv) with
| [] -> begin
expr
end
| uu____756 -> begin
(FStar_List.append new_fv ((FStar_Extraction_JavaScript_Ast.JSS_Block (expr))::[]))
end)))
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e var) -> begin
(

let expr = (translate_expr_pure e env)
in (get_res expr []))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____762, uu____763, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____765); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let isEqName = (isInEnv env name)
in (

let env = (match (isEqName) with
| true -> begin
env
end
| uu____779 -> begin
(extendEnv env (([]), (name)) tys)
end)
in (

let c = (translate_expr continuation var lstmt env isDecl)
in (

let uu____783 = (is_pure_expr body ((name), (None)))
in (match (uu____783) with
| true -> begin
(

let var_decl_q = (match ((isMutable tys)) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JSV_Let
end
| uu____788 -> begin
FStar_Extraction_JavaScript_Ast.JSV_Const
end)
in (

let c = (let _0_414 = (let _0_413 = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((let _0_412 = (let _0_411 = Some ((translate_expr_pure body env))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (_0_411)))
in ((_0_412), (var_decl_q))))
in (_0_413)::[])
in (FStar_List.append _0_414 c))
in (match (isEqName) with
| true -> begin
(FStar_Extraction_JavaScript_Ast.JSS_Block (c))::[]
end
| uu____797 -> begin
c
end)))
end
| uu____798 -> begin
(translate_expr body ((name), (None)) c env false)
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____800) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args = (FStar_List.map (fun uu____822 -> (match (uu____822) with
| ((n, uu____828), t) -> begin
FStar_Extraction_JavaScript_Ast.JGP_Identifier ((let _0_415 = Some ((translate_type t None env))
in ((n), (_0_415))))
end)) args)
in (

let is_failwith = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_App (expr, uu____836) -> begin
(match (expr.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (let _0_416 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_416 = "failwith")) -> begin
true
end
| uu____840 -> begin
false
end)
end
| uu____841 -> begin
false
end)
in (

let body_t = (match (is_failwith) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Not yet implemented!")), ("")))))::[])
end
| uu____843 -> begin
(

let uu____844 = (is_pure_expr body var)
in (match (uu____844) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JS_BodyExpression ((translate_expr_pure body env))
end
| uu____846 -> begin
FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((let _0_417 = (translate_expr body (("_res"), (None)) ((FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))::[]) env true)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _0_417)))
end))
end)
in (

let uu____854 = (match ((Prims.snd var)) with
| None -> begin
((None), (None))
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (uu____876, t2, lp) -> begin
((Some (t2)), (lp))
end
| uu____898 -> begin
((None), (None))
end)
end)
in (match (uu____854) with
| (ret_t, lp_generic) -> begin
(

let expr = FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (((None), (args), (body_t), (ret_t), (lp_generic)))
in (

let expr = (match (isDecl) with
| true -> begin
(FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((((Prims.fst var)), (None)))), (expr)))))::[]
end
| uu____929 -> begin
(FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((((Prims.fst var)), (None)))), (Some (expr)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::[]
end)
in (FStar_List.append expr lstmt)))
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let s1 = FStar_Extraction_JavaScript_Ast.JSS_Block ((translate_expr s1 var [] env true))
in (

let s2 = (match (s2) with
| Some (v) -> begin
Some (FStar_Extraction_JavaScript_Ast.JSS_Block ((translate_expr v var [] env true)))
end
| None -> begin
None
end)
in (

let c = (

let uu____948 = (is_pure_expr cond var)
in (match (uu____948) with
| true -> begin
(let _0_419 = FStar_Extraction_JavaScript_Ast.JSS_If ((let _0_418 = (translate_expr_pure cond env)
in ((_0_418), (s1), (s2))))
in (_0_419)::[])
end
| uu____952 -> begin
(let _0_420 = (translate_expr cond (("_cond"), (None)) ((FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (None)))), (s1), (s2))))::[]) env true)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _0_420))
end))
in (

let c = (match (isDecl) with
| true -> begin
c
end
| uu____964 -> begin
(FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) c)
end)
in (FStar_List.append c lstmt)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____969) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____974) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(

let var = (((Prims.fst var)), (Some (FStar_Extraction_JavaScript_Ast.JST_Any)))
in (translate_expr in_e var lstmt env isDecl))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let match_e = (let _0_421 = (Prims.fst (FStar_Extraction_ML_Syntax.gensym ()))
in ((_0_421), (None)))
in (

let c = (

let uu____1011 = (is_pure_expr e_in var)
in (match (uu____1011) with
| true -> begin
(let _0_426 = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((let _0_423 = (let _0_422 = Some ((translate_expr_pure e_in env))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (match_e)), (_0_422)))
in ((_0_423), (FStar_Extraction_JavaScript_Ast.JSV_Const))))
in (let _0_425 = (let _0_424 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (match_e)) var env)
in (_0_424)::[])
in (_0_426)::_0_425))
end
| uu____1018 -> begin
(let _0_429 = (let _0_428 = (let _0_427 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (match_e)) var env)
in (_0_427)::[])
in (translate_expr e_in match_e _0_428 env true))
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (match_e)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _0_429))
end))
in (

let c = (match (isDecl) with
| true -> begin
c
end
| uu____1026 -> begin
(FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) c)
end)
in (FStar_List.append c lstmt))))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(

let rec translate_seq = (fun l -> (match (l) with
| [] -> begin
(failwith "Empty list in [MLE_Seq]")
end
| (x)::[] -> begin
(translate_expr x var [] env isDecl)
end
| (hd)::tl -> begin
(let _0_430 = (translate_seq tl)
in (translate_expr hd (("_"), (None)) _0_430 env false))
end))
in (let _0_431 = (translate_seq ls)
in (FStar_List.append _0_431 lstmt)))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let uu____1051 = (create_pure_args args var env)
in (match (uu____1051) with
| (args, new_fv) -> begin
(

let expr = (translate_arg_app e args var env)
in (get_res expr new_fv))
end))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(

let uu____1074 = (create_pure_args lexpr var env)
in (match (uu____1074) with
| (lexpr, new_fv) -> begin
(

let expr = (match (c) with
| x when ((x = "Cons") || (x = "Nil")) -> begin
(match (lexpr) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSE_Array (None)
end
| (hd)::tl -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Array (Some ((hd)::[]))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("concat"), (None))))))), (tl)))
end)
end
| x when ((x = "Some") || (x = "None")) -> begin
(match (lexpr) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| (hd)::tl -> begin
(FStar_List.nth lexpr (Prims.parse_int "0"))
end)
end
| uu____1099 -> begin
FStar_Extraction_JavaScript_Ast.JSE_Object ((let _0_435 = (FStar_List.mapi (fun i x -> FStar_Extraction_JavaScript_Ast.JSPO_Property ((let _0_434 = FStar_Extraction_JavaScript_Ast.JSO_Identifier ((let _0_433 = (let _0_432 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_432))
in ((_0_433), (None))))
in ((_0_434), (x), (FStar_Extraction_JavaScript_Ast.JSO_Init))))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _0_435)))
end)
in (get_res expr new_fv))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let uu____1114 = (FStar_List.fold_left (fun uu____1125 uu____1126 -> (match (((uu____1125), (uu____1126))) with
| ((lexpr, lnew_fv), (id, x)) -> begin
(

let uu____1157 = (create_pure_args ((x)::[]) var env)
in (match (uu____1157) with
| (expr, fv) -> begin
(let _0_439 = (let _0_438 = (let _0_437 = FStar_Extraction_JavaScript_Ast.JSPO_Property ((let _0_436 = (FStar_List.nth expr (Prims.parse_int "0"))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_0_436), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in (_0_437)::[])
in (FStar_List.append _0_438 lexpr))
in ((_0_439), ((FStar_List.append fv lnew_fv))))
end))
end)) (([]), ([])) fields)
in (match (uu____1114) with
| (create_fields, new_fv) -> begin
(

let expr = FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))
in (get_res expr new_fv))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let uu____1188 = (FStar_List.fold_left (fun uu____1197 x -> (match (uu____1197) with
| (lexpr, lnew_fv) -> begin
(

let uu____1213 = (create_pure_args ((x)::[]) var env)
in (match (uu____1213) with
| (expr, fv) -> begin
(((FStar_List.append expr lexpr)), ((FStar_List.append fv lnew_fv)))
end))
end)) (([]), ([])) lexp)
in (match (uu____1188) with
| (create_fields, new_fv) -> begin
(

let expr = FStar_Extraction_JavaScript_Ast.JSE_Array (Some (create_fields))
in (get_res expr new_fv))
end))
end
| uu____1241 -> begin
(failwith "todo: translation ml-expr")
end)))
and create_pure_args : FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  env  ->  (FStar_Extraction_JavaScript_Ast.expression_t Prims.list * FStar_Extraction_JavaScript_Ast.statement_t Prims.list) = (fun args var env -> (FStar_List.fold_left (fun uu____1254 x -> (match (uu____1254) with
| (lexpr, lnew_fv) -> begin
(match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), uu____1276) when ((c = "Nil") || (c = "None")) -> begin
(let _0_444 = (let _0_443 = (let _0_442 = FStar_Extraction_JavaScript_Ast.JSE_TypeCast ((let _0_441 = (translate_expr_pure x env)
in (let _0_440 = (translate_type x.FStar_Extraction_ML_Syntax.mlty None env)
in ((_0_441), (_0_440)))))
in (_0_442)::[])
in (FStar_List.append _0_443 lexpr))
in ((_0_444), (lnew_fv)))
end
| uu____1287 -> begin
(

let uu____1288 = (is_pure_expr x var)
in (match (uu____1288) with
| true -> begin
(let _0_447 = (let _0_446 = (let _0_445 = (translate_expr_pure x env)
in (_0_445)::[])
in (FStar_List.append _0_446 lexpr))
in ((_0_447), (lnew_fv)))
end
| uu____1296 -> begin
(

let fv_x = (Prims.fst (FStar_Extraction_ML_Syntax.gensym ()))
in (

let c = (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1301) -> begin
(let _0_450 = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((let _0_449 = (let _0_448 = Some ((translate_expr_pure x env))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (_0_448)))
in ((_0_449), (FStar_Extraction_JavaScript_Ast.JSV_Const))))
in (_0_450)::[])
end
| uu____1307 -> begin
(translate_expr x ((fv_x), (None)) [] env false)
end)
in (((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None))))::[]) lexpr)), ((FStar_List.append c lnew_fv)))))
end))
end)
end)) (([]), ([])) args))
and translate_arg_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list  ->  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  env  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e args var env -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Binary ((let _0_453 = (FStar_Util.must (mk_op_bin op))
in (let _0_452 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _0_451 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_0_453), (_0_452), (_0_451))))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Logical ((let _0_456 = (FStar_Util.must (mk_op_bool op))
in (let _0_455 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _0_454 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_0_456), (_0_455), (_0_454))))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Unary ((let _0_458 = (FStar_Util.must (mk_op_un op))
in (let _0_457 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_0_458), (_0_457)))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((let _0_459 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_459 = "FStar.Buffer.op_Array_Access")) || (let _0_460 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_460 = "FStar.Buffer.index"))) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_462 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _0_461 = FStar_Extraction_JavaScript_Ast.JSPM_Expression ((FStar_List.nth args (Prims.parse_int "1")))
in ((_0_462), (_0_461)))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((let _0_463 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_463 = "FStar.Buffer.op_Array_Assignment")) || (let _0_464 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_464 = "FStar.Buffer.upd"))) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Assignment ((let _0_468 = FStar_Extraction_JavaScript_Ast.JGP_Expression (FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_466 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _0_465 = FStar_Extraction_JavaScript_Ast.JSPM_Expression ((FStar_List.nth args (Prims.parse_int "1")))
in ((_0_466), (_0_465))))))
in (let _0_467 = (FStar_List.nth args (Prims.parse_int "2"))
in ((_0_468), (_0_467)))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((let _0_469 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_469 = "FStar.ST.op_Bang")) || (let _0_470 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_470 = "FStar.ST.read"))) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_471 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_0_471), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0"))))))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((let _0_472 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_472 = "FStar.ST.op_Colon_Equals")) || (let _0_473 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_473 = "FStar.ST.write"))) -> begin
(

let expr = FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_474 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_0_474), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0"))))))))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment ((let _0_475 = (FStar_List.nth args (Prims.parse_int "1"))
in ((FStar_Extraction_JavaScript_Ast.JGP_Expression (expr)), (_0_475)))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (let _0_476 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_476 = "FStar.ST.alloc")) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Array (Some ((let _0_477 = (FStar_List.nth args (Prims.parse_int "0"))
in (_0_477)::[])))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(

let path = (FStar_String.concat "_" path)
in (

let name = (match (((path = env.module_name) || (path = ""))) with
| true -> begin
function_name
end
| uu____1341 -> begin
(Prims.strcat path (Prims.strcat "." function_name))
end)
in FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____1345) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))
end
| uu____1348 -> begin
(

let uu____1349 = (is_pure_expr e var)
in (match (uu____1349) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call ((let _0_478 = (translate_expr_pure e env)
in ((_0_478), (args))))
end
| uu____1352 -> begin
(failwith "todo: translation [MLE_App]")
end))
end))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  env  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e env -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____1357) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, name) -> begin
(

let path = (FStar_String.concat "_" path)
in (

let name = (match (((path = env.module_name) || (path = ""))) with
| true -> begin
name
end
| uu____1365 -> begin
(Prims.strcat path (Prims.strcat "." name))
end)
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Array (Some ((FStar_List.map (fun x -> (translate_expr_pure x env)) lexp)))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun uu____1385 -> (match (uu____1385) with
| (id, x) -> begin
FStar_Extraction_JavaScript_Ast.JSPO_Property ((let _0_479 = (translate_expr_pure x env)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_0_479), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(match (c) with
| x when ((x = "Cons") || (x = "Nil")) -> begin
(match (lexpr) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSE_Array (None)
end
| (hd)::tl -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call ((let _0_483 = FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_481 = FStar_Extraction_JavaScript_Ast.JSE_Array (Some ((let _0_480 = (translate_expr_pure hd env)
in (_0_480)::[])))
in ((_0_481), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("concat"), (None)))))))
in (let _0_482 = (FStar_List.map (fun x -> (translate_expr_pure x env)) tl)
in ((_0_483), (_0_482)))))
end)
end
| x when ((x = "Some") || (x = "None")) -> begin
(match (lexpr) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| (hd)::tl -> begin
(let _0_484 = (FStar_List.map (fun x -> (translate_expr_pure x env)) lexpr)
in (FStar_List.nth _0_484 (Prims.parse_int "0")))
end)
end
| uu____1416 -> begin
FStar_Extraction_JavaScript_Ast.JSE_Object ((let _0_489 = (FStar_List.mapi (fun i x -> FStar_Extraction_JavaScript_Ast.JSPO_Property ((let _0_488 = FStar_Extraction_JavaScript_Ast.JSO_Identifier ((let _0_486 = (let _0_485 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_485))
in ((_0_486), (None))))
in (let _0_487 = (translate_expr_pure x env)
in ((_0_488), (_0_487), (FStar_Extraction_JavaScript_Ast.JSO_Init)))))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _0_489)))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, uu____1422, uu____1423) -> begin
(translate_expr_pure e env)
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args = (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), uu____1433) when ((c = "Nil") || (c = "None")) -> begin
FStar_Extraction_JavaScript_Ast.JSE_TypeCast ((let _0_491 = (translate_expr_pure x env)
in (let _0_490 = (translate_type x.FStar_Extraction_ML_Syntax.mlty None env)
in ((_0_491), (_0_490)))))
end
| uu____1442 -> begin
(translate_expr_pure x env)
end)) args)
in (translate_arg_app e args ((""), (None)) env))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, (path, name)) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_492 = (translate_expr_pure expr env)
in ((_0_492), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" name)), (None)))))))
end
| uu____1453 -> begin
(failwith "todo: translation ml-expr-pure")
end))
and translate_match : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  env  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb match_e var env -> (match (lb) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end
| ((p, guard, expr_r))::tl -> begin
(

let expr_t = (

let uu____1486 = (is_pure_expr expr_r var)
in (match (uu____1486) with
| true -> begin
(let _0_495 = FStar_Extraction_JavaScript_Ast.JSE_Assignment ((let _0_493 = (translate_expr_pure expr_r env)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_0_493))))
in (FStar_All.pipe_right _0_495 (fun _0_494 -> FStar_Extraction_JavaScript_Ast.JSS_Expression (_0_494))))
end
| uu____1488 -> begin
(let _0_497 = (translate_expr expr_r var [] env true)
in (FStar_All.pipe_right _0_497 (fun _0_496 -> FStar_Extraction_JavaScript_Ast.JSS_Seq (_0_496))))
end))
in (let _0_498 = (translate_match tl match_e var env)
in (translate_pat_guard ((p), (guard)) match_e expr_t _0_498 env)))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  env  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun uu____1491 match_e s1 s2 env -> (match (uu____1491) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p match_e s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = FStar_Extraction_JavaScript_Ast.JSS_If ((let _0_499 = (translate_expr_pure v_guard env)
in ((_0_499), (s1), (Some (s2)))))
in (translate_pat p match_e cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p match_e s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____1511) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Seq ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (match_e)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
FStar_Extraction_JavaScript_Ast.JSS_If ((let _0_501 = FStar_Extraction_JavaScript_Ast.JSE_Binary ((let _0_500 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (match_e), (_0_500))))
in ((_0_501), (s1), (Some (s2)))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((path, c), lp) -> begin
(

let rec translate_p_ctor = (fun lp match_e s1 s2 i -> (

let new_fv_x = (match (c) with
| x when (x = "Some") -> begin
match_e
end
| x when ((x = "Cons") && (i = (Prims.parse_int "0"))) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member (((match_e), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0")))))))
end
| x when ((x = "Cons") && (i = (Prims.parse_int "1"))) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member (((match_e), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("slice(1)"), (None))))))
end
| uu____1552 -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_504 = FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((let _0_503 = (let _0_502 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_502))
in ((_0_503), (None))))
in ((match_e), (_0_504))))
end)
in (match (lp) with
| [] -> begin
s1
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _0_505 = (translate_p_ctor tl match_e s1 s2 (i + (Prims.parse_int "1")))
in (translate_pat hd new_fv_x _0_505 s2))
end)))
in (

let if_stmt = (fun if_cond -> FStar_Extraction_JavaScript_Ast.JSS_If ((let _0_506 = (translate_p_ctor lp match_e s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_0_506), (Some (s2))))))
in (match (c) with
| x when (x = "Cons") -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_GreaterThan), (FStar_Extraction_JavaScript_Ast.JSE_Member (((match_e), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("length"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0"))))))))
end
| x when (x = "Nil") -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_Equal), (FStar_Extraction_JavaScript_Ast.JSE_Member (((match_e), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("length"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0"))))))))
end
| x when (x = "Some") -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_NotEqual), (match_e), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))))))
end
| x when (x = "None") -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_Equal), (match_e), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))))))
end
| uu____1569 -> begin
(

let isSimple = (match (match_e) with
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (uu____1571) -> begin
true
end
| uu____1575 -> begin
false
end)
in (match (isSimple) with
| true -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((match_e), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))))
end
| uu____1577 -> begin
(

let new_name = (Prims.fst (FStar_Extraction_ML_Syntax.gensym ()))
in (

let if_cond = FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))
in FStar_Extraction_JavaScript_Ast.JSS_Seq ((let _0_509 = (let _0_508 = FStar_Extraction_JavaScript_Ast.JSS_If ((let _0_507 = (translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))) s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_0_507), (Some (s2)))))
in (_0_508)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((new_name), (None)))), (Some (match_e)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::_0_509))))
end))
end)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (lp) -> begin
(

let rec translate_p_branch = (fun lp match_e s1 s2 -> (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_branch")
end
| (x)::[] -> begin
(translate_pat x match_e s1 s2)
end
| (hd)::tl -> begin
(let _0_510 = (translate_p_branch tl match_e s1 s2)
in (translate_pat hd match_e s1 _0_510))
end))
in (translate_p_branch lp match_e s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, lp) -> begin
(

let rec translate_p_record = (fun lp match_e s1 s2 -> (

let new_fv_x = (fun n -> FStar_Extraction_JavaScript_Ast.JSE_Member (((match_e), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" n)), (None)))))))
in (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_record")
end
| (x)::[] -> begin
(translate_pat (Prims.snd x) (new_fv_x (Prims.fst x)) s1 s2)
end
| (hd)::tl -> begin
(let _0_511 = (translate_p_record tl match_e s1 s2)
in (translate_pat (Prims.snd hd) (new_fv_x (Prims.fst hd)) _0_511 s2))
end)))
in (translate_p_record lp match_e s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(

let rec translate_p_tuple = (fun lp d match_e s1 s2 -> (

let new_fv_x = FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_513 = FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal ((let _0_512 = (FStar_Util.string_of_int d)
in ((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int d))), (_0_512)))))
in ((match_e), (_0_513))))
in (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_tuple")
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _0_514 = (translate_p_tuple tl (d + (Prims.parse_int "1")) match_e s1 s2)
in (translate_pat hd new_fv_x _0_514 s2))
end)))
in (translate_p_tuple lp (Prims.parse_int "0") match_e s1 s2))
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, uu____1690) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____1698) -> begin
(failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____1700) -> begin
(failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlsymbol Prims.list Prims.option  ->  env  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t lp_generic env -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, uu____1708) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((id), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
FStar_Extraction_JavaScript_Ast.JST_Tuple ((FStar_List.map (fun x -> (translate_type x lp_generic env)) lt))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, e_tag, t2) -> begin
(

let t2 = (match ((e_tag = FStar_Extraction_ML_Syntax.E_GHOST)) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JST_Null
end
| uu____1719 -> begin
(translate_type t2 None env)
end)
in FStar_Extraction_JavaScript_Ast.JST_Function ((let _0_517 = (let _0_516 = (let _0_515 = (translate_type t1 None env)
in (((("_1"), (None))), (_0_515)))
in (_0_516)::[])
in ((_0_517), (t2), (lp_generic)))))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) when (let _0_518 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_518 = "FStar.ST.ref")) -> begin
FStar_Extraction_JavaScript_Ast.JST_Array ((let _0_519 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_type _0_519 lp_generic env)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1748, p) when (let _0_520 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_520 = "FStar.Buffer.buffer")) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic ((("FStar_Buffer.buffer"), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1755, p) when (let _0_521 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_521 = "FStar.Ghost.erased")) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
(match ((is_standart_type name)) with
| true -> begin
(FStar_Util.must (mk_standart_type name))
end
| uu____1769 -> begin
(match ((FStar_Option.isSome (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name))))) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JST_Tuple ((FStar_List.map (fun x -> (translate_type x lp_generic env)) args))
end
| uu____1772 -> begin
(

let args_t = (match (args) with
| [] -> begin
None
end
| uu____1779 -> begin
(let _0_523 = (FStar_List.map (fun x -> (translate_type x lp_generic env)) args)
in (FStar_All.pipe_right _0_523 (fun _0_522 -> Some (_0_522))))
end)
in (

let path = (FStar_String.concat "_" path)
in (

let name = (match (((path = env.module_name) || (path = ""))) with
| true -> begin
name
end
| uu____1788 -> begin
(Prims.strcat path (Prims.strcat "." name))
end)
in FStar_Extraction_JavaScript_Ast.JST_Generic (((name), (args_t))))))
end)
end)
end))




