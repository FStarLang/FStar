
open Prims

type file =
(Prims.string * FStar_Extraction_JavaScript_Ast.t)

type env_t =
{names : name Prims.list; module_name : Prims.string; import_module_names : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let empty : Prims.string  ->  env_t = (fun module_name -> {names = []; module_name = module_name; import_module_names = []})


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
in {names = ({pretty = n; mut = (isMutable typ)})::env.names; module_name = uu___141_148.module_name; import_module_names = uu___141_148.import_module_names})
end
| uu____149 -> begin
(

let n = (Prims.strcat path (Prims.strcat "." n))
in (match ((not ((FStar_List.existsb (fun x -> (x = path)) env.import_module_names)))) with
| true -> begin
(

let uu___142_152 = env
in {names = ({pretty = n; mut = (isMutable typ)})::env.names; module_name = uu___142_152.module_name; import_module_names = (path)::env.import_module_names})
end
| uu____153 -> begin
(

let uu___143_154 = env
in {names = ({pretty = n; mut = (isMutable typ)})::env.names; module_name = uu___143_154.module_name; import_module_names = uu___143_154.import_module_names})
end))
end))
end))


let addImportModule : env_t  ->  (Prims.string Prims.list * Prims.string)  ->  (Prims.string * env_t) = (fun env uu____165 -> (match (uu____165) with
| (path, name) -> begin
(

let path = (FStar_String.concat "_" path)
in (match (((path = env.module_name) || (path = ""))) with
| true -> begin
((name), (env))
end
| uu____178 -> begin
(

let name = (Prims.strcat path (Prims.strcat "." name))
in (match ((not ((FStar_List.existsb (fun x -> (x = path)) env.import_module_names)))) with
| true -> begin
((name), ((

let uu___144_183 = env
in {names = uu___144_183.names; module_name = uu___144_183.module_name; import_module_names = (path)::env.import_module_names})))
end
| uu____184 -> begin
((name), (env))
end))
end))
end))


let findEnv : env_t  ->  Prims.string  ->  Prims.int = (fun env name -> (FStar_List.index (fun x -> (x.pretty = name)) env.names))


let isInEnv : env_t  ->  Prims.string  ->  Prims.bool = (fun env name -> (FStar_List.existsb (fun x -> (x.pretty = name)) env.names))


let rec is_pure_expr = (fun e var -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (n, uu____218) -> begin
(n <> (Prims.fst var))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, uu____220) -> begin
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
| FStar_Extraction_ML_Syntax.MLE_Record (uu____229, lne) -> begin
(not ((let _0_377 = (FStar_List.map (fun uu____241 -> (match (uu____241) with
| (n, e) -> begin
(is_pure_expr e var)
end)) lne)
in (FStar_List.contains false _0_377))))
end
| FStar_Extraction_ML_Syntax.MLE_App (uu____246, args) -> begin
(not ((let _0_378 = (FStar_List.map (fun x -> (is_pure_expr x var)) args)
in (FStar_List.contains false _0_378))))
end
| uu____251 -> begin
false
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun uu____406 -> (match (uu____406) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let uu____437 = m
in (match (uu____437) with
| ((prefix, final), uu____449, uu____450) -> begin
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
and translate_module : env_t  ->  ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun env uu____471 -> (match (uu____471) with
| (module_name, modul, uu____483) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let update_env = (fun uu____506 -> (

let uu___147_507 = env
in {names = []; module_name = uu___147_507.module_name; import_module_names = uu___147_507.import_module_names}))
in (

let res = (FStar_List.filter_map (fun d -> (translate_decl (update_env ()) d)) decls)
in (

let td = (FStar_List.map (fun uu____519 -> (match (uu____519) with
| (x, e) -> begin
x
end)) res)
in (

let lmodules = (FStar_List.collect (fun uu____528 -> (match (uu____528) with
| (x, e) -> begin
e.import_module_names
end)) res)
in (

let lmodules = (FStar_List.fold_left (fun acc m -> (match ((FStar_List.existsb (fun x -> (x = m)) acc)) with
| true -> begin
acc
end
| uu____542 -> begin
(m)::acc
end)) [] lmodules)
in (

let create_module_imports = (let _0_383 = (let _0_381 = (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (((m), (None)))) lmodules)
in (FStar_All.pipe_right _0_381 (fun _0_380 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_0_380))))
in (FStar_All.pipe_right _0_383 (fun _0_382 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_0_382))))
in (FStar_List.append ((create_module_imports)::[]) td)))))))
end
| uu____547 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in ((env.module_name), (program)))
end))
and translate_decl : env_t  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  (FStar_Extraction_JavaScript_Ast.source_t * env_t) Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (uu____561, c_flag, lfunc) -> begin
(

let for1 = (fun uu____574 env -> (match (uu____574) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, uu____580); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let uu____586 = (match (((not (pt)) || unit_b)) with
| true -> begin
((None), (env))
end
| uu____594 -> begin
(match (tys) with
| None -> begin
((None), (env))
end
| Some (lp, ty) -> begin
(

let lp_generic = (match (lp) with
| [] -> begin
None
end
| uu____609 -> begin
Some ((FStar_List.map (fun uu____613 -> (match (uu____613) with
| (id, uu____617) -> begin
id
end)) lp))
end)
in (

let uu____618 = (translate_type ty lp_generic env)
in (match (uu____618) with
| (t, env) -> begin
((Some (t)), (env))
end)))
end)
end)
in (match (uu____586) with
| (t, env) -> begin
(

let is_private = (FStar_List.contains FStar_Extraction_ML_Syntax.Private c_flag)
in (

let uu____635 = (

let uu____639 = (is_pure_expr expr ((name), (None)))
in (match (uu____639) with
| true -> begin
(

let var_decl_q = (match ((isMutable tys)) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JSV_Let
end
| uu____646 -> begin
FStar_Extraction_JavaScript_Ast.JSV_Const
end)
in (

let env = (extendEnv env (([]), (name)) tys)
in (

let uu____649 = (translate_expr_pure expr env)
in (match (uu____649) with
| (r, env) -> begin
(((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (Some (r)))), (var_decl_q))))::[]), (env))
end))))
end
| uu____663 -> begin
(translate_expr expr ((name), (t)) [] env false)
end))
in (match (uu____635) with
| (c, env) -> begin
(match (is_private) with
| true -> begin
((c), (env))
end
| uu____676 -> begin
(((FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (FStar_Extraction_JavaScript_Ast.JSS_Block (c))), (FStar_Extraction_JavaScript_Ast.ExportValue))))::[]), (env))
end)
end)))
end))
end))
in (

let uu____678 = (FStar_List.fold_left (fun uu____685 x -> (match (uu____685) with
| (r, e) -> begin
(

let update_env = (fun uu____700 -> (

let uu___148_701 = e
in {names = []; module_name = uu___148_701.module_name; import_module_names = uu___148_701.import_module_names}))
in (

let uu____702 = (for1 x (update_env ()))
in (match (uu____702) with
| (r1, e1) -> begin
(((FStar_List.append r ((FStar_Extraction_JavaScript_Ast.JSS_Seq (r1))::[]))), (e1))
end)))
end)) (([]), (env)) lfunc)
in (match (uu____678) with
| (r, env) -> begin
Some (((FStar_Extraction_JavaScript_Ast.JS_Statement (FStar_Extraction_JavaScript_Ast.JSS_Block (r))), (env)))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____724) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((uu____727, name, uu____729, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| uu____756 -> begin
Some ((FStar_List.map (fun uu____760 -> (match (uu____760) with
| (id, uu____764) -> begin
id
end)) tparams))
end)
in (

let forbody = (fun body -> (

let get_export = (fun stmt -> FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (stmt)), (FStar_Extraction_JavaScript_Ast.ExportType))))
in (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(

let uu____778 = (translate_type t tparams env)
in (match (uu____778) with
| (t, env) -> begin
(((get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (t)))))), (env))
end))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let uu____804 = (FStar_List.fold_left (fun uu____817 uu____818 -> (match (((uu____817), (uu____818))) with
| ((r, e), (n, t)) -> begin
(

let uu____855 = (translate_type t tparams e)
in (match (uu____855) with
| (r1, e1) -> begin
(((FStar_List.append r ((((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (r1)))::[]))), (e1))
end))
end)) (([]), (env)) fields)
in (match (uu____804) with
| (fields_t, env) -> begin
(((get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((FStar_List.append tag fields_t)))))))), (env))
end)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields env -> (FStar_List.fold_left (fun uu____936 t -> (match (uu____936) with
| (i, r, e) -> begin
(

let uu____959 = (translate_type t tparams e)
in (match (uu____959) with
| (r1, e1) -> begin
(let _0_389 = (let _0_388 = (let _0_387 = (let _0_386 = FStar_Extraction_JavaScript_Ast.JSO_Identifier ((let _0_385 = (let _0_384 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_384))
in ((_0_385), (None))))
in ((_0_386), (r1)))
in (_0_387)::[])
in (FStar_List.append r _0_388))
in (((i + (Prims.parse_int "1"))), (_0_389), (e1)))
end))
end)) (((Prims.parse_int "0")), ([]), (env)) fields))
in (

let uu____985 = (FStar_List.fold_left (fun uu____995 uu____996 -> (match (((uu____995), (uu____996))) with
| ((r, e), (n, l)) -> begin
(

let uu____1026 = (fields_t l e)
in (match (uu____1026) with
| (uu____1036, r1, e1) -> begin
(((FStar_List.append r (((get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((n), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((FStar_List.append (tag n) r1))))))))::[]))), (e1))
end))
end)) (([]), (env)) lfields)
in (match (uu____985) with
| (lfields_t, env) -> begin
(

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _0_391 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((x), (None)))) t)
in (FStar_All.pipe_right _0_391 (fun _0_390 -> Some (_0_390))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun uu____1084 -> (match (uu____1084) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((n), (tparams_gen)))
end)) lfields)
in (

let union_t = (get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Union (lnames))))))
in ((FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append lfields_t ((union_t)::[])))), (env)))))
end))))
end)))
in (

let uu____1101 = (match (body) with
| None -> begin
(failwith "todo: translate_decl [MLM_Ty] with empty body")
end
| Some (v) -> begin
(forbody v)
end)
in (match (uu____1101) with
| (body_t, env) -> begin
Some (((FStar_Extraction_JavaScript_Ast.JS_Statement (body_t)), (env)))
end))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (uu____1116) -> begin
(failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (uu____1120) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
Some (((FStar_Extraction_JavaScript_Ast.JS_Statement (FStar_Extraction_JavaScript_Ast.JSS_Block ([]))), (env)))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (uu____1128) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  env_t  ->  Prims.bool  ->  (FStar_Extraction_JavaScript_Ast.statement_t Prims.list * env_t) = (fun e var lstmt env isDecl -> (

let get_res = (fun expr new_fv env -> (

let is_inEnv = (isInEnv env (Prims.fst var))
in (

let uu____1164 = (

let res = (fun e -> (

let env = (extendEnv env (([]), ((Prims.fst var))) None)
in (match (is_inEnv) with
| true -> begin
(((FStar_Extraction_JavaScript_Ast.JSS_Block (e))::[]), (env))
end
| uu____1186 -> begin
((e), (env))
end)))
in (match (expr) with
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (uu____1191) -> begin
(match (isDecl) with
| true -> begin
(match (((Prims.fst var) = "_")) with
| true -> begin
(((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_Expression (expr))::[]) lstmt)), (env))
end
| uu____1202 -> begin
(((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_Expression (expr))::(FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))))))::[]) lstmt)), (env))
end)
end
| uu____1204 -> begin
(res (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_Expression (expr))::(FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) lstmt))
end)
end
| uu____1209 -> begin
(match (isDecl) with
| true -> begin
(((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (expr)))))::[]) lstmt)), (env))
end
| uu____1214 -> begin
(res (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (expr)))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) lstmt))
end)
end))
in (match (uu____1164) with
| (expr, env) -> begin
(((match (new_fv) with
| [] -> begin
expr
end
| uu____1228 -> begin
(match (is_inEnv) with
| true -> begin
(FStar_List.append new_fv expr)
end
| uu____1231 -> begin
(FStar_List.append new_fv ((FStar_Extraction_JavaScript_Ast.JSS_Block (expr))::[]))
end)
end)), (env))
end))))
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e var) -> begin
(

let uu____1237 = (translate_expr_pure e env)
in (match (uu____1237) with
| (expr, env) -> begin
(get_res expr [] env)
end))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____1245, uu____1246, ({FStar_Extraction_ML_Syntax.mllb_name = (name, uu____1248); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let isEqName = (isInEnv env name)
in (

let env = (extendEnv env (([]), (name)) tys)
in (

let uu____1263 = (is_pure_expr body ((name), (None)))
in (match (uu____1263) with
| true -> begin
(

let var_decl_q = (match ((isMutable tys)) with
| true -> begin
FStar_Extraction_JavaScript_Ast.JSV_Let
end
| uu____1270 -> begin
FStar_Extraction_JavaScript_Ast.JSV_Const
end)
in (

let uu____1271 = (translate_expr_pure body env)
in (match (uu____1271) with
| (r, env) -> begin
(

let uu____1279 = (translate_expr continuation var lstmt env isDecl)
in (match (uu____1279) with
| (c, env1) -> begin
(

let c = (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (r)))), (var_decl_q))))::[]) c)
in (

let env = (

let uu___149_1298 = env
in {names = uu___149_1298.names; module_name = uu___149_1298.module_name; import_module_names = (FStar_List.append env.import_module_names env1.import_module_names)})
in (match (isEqName) with
| true -> begin
(((FStar_Extraction_JavaScript_Ast.JSS_Block (c))::[]), (env))
end
| uu____1303 -> begin
((c), (env))
end)))
end))
end)))
end
| uu____1305 -> begin
(

let uu____1306 = (translate_expr continuation var lstmt env isDecl)
in (match (uu____1306) with
| (c, env1) -> begin
(

let uu____1317 = (translate_expr body ((name), (None)) c env false)
in (match (uu____1317) with
| (r, env) -> begin
(

let env = (

let uu___150_1330 = env
in {names = uu___150_1330.names; module_name = uu___150_1330.module_name; import_module_names = (FStar_List.append env.import_module_names env1.import_module_names)})
in ((r), (env)))
end))
end))
end))))
end
| FStar_Extraction_ML_Syntax.MLE_Let (uu____1332) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let uu____1350 = (FStar_List.fold_left (fun uu____1361 uu____1362 -> (match (((uu____1361), (uu____1362))) with
| ((r, e), ((n, uu____1383), t)) -> begin
(

let uu____1396 = (translate_type t None e)
in (match (uu____1396) with
| (r1, e1) -> begin
(((FStar_List.append r ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (Some (r1)))))::[]))), (e1))
end))
end)) (([]), (env)) args)
in (match (uu____1350) with
| (args, env) -> begin
(

let is_failwith = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_App (expr, uu____1417) -> begin
(match (expr.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (let _0_392 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_392 = "failwith")) -> begin
true
end
| uu____1421 -> begin
false
end)
end
| uu____1422 -> begin
false
end)
in (

let uu____1423 = (match (is_failwith) with
| true -> begin
((FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Not yet implemented!")), ("")))))::[])), (env))
end
| uu____1428 -> begin
(

let uu____1429 = (is_pure_expr body var)
in (match (uu____1429) with
| true -> begin
(

let uu____1433 = (translate_expr_pure body env)
in (match (uu____1433) with
| (r, env1) -> begin
((FStar_Extraction_JavaScript_Ast.JS_BodyExpression (r)), (env1))
end))
end
| uu____1440 -> begin
(

let uu____1441 = (translate_expr body (("_res"), (None)) ((FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))::[]) env true)
in (match (uu____1441) with
| (t1, env1) -> begin
((FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) t1))), (env1))
end))
end))
end)
in (match (uu____1423) with
| (body_t, env1) -> begin
(

let uu____1463 = (match ((Prims.snd var)) with
| None -> begin
((None), (None))
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (uu____1485, t2, lp) -> begin
((Some (t2)), (lp))
end
| uu____1507 -> begin
((None), (None))
end)
end)
in (match (uu____1463) with
| (ret_t, lp_generic) -> begin
(

let expr = FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (((None), (args), (body_t), (ret_t), (lp_generic)))
in (

let uu____1535 = (match (isDecl) with
| true -> begin
(((FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((((Prims.fst var)), (None)))), (expr)))))::[]), (env))
end
| uu____1545 -> begin
(

let env = (extendEnv env (([]), ((Prims.fst var))) None)
in (((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((((Prims.fst var)), (None)))), (Some (expr)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::[]), (env)))
end)
in (match (uu____1535) with
| (expr, env) -> begin
(

let env = (

let uu___151_1566 = env
in {names = uu___151_1566.names; module_name = uu___151_1566.module_name; import_module_names = (FStar_List.append env.import_module_names env1.import_module_names)})
in (((FStar_List.append expr lstmt)), (env)))
end)))
end))
end)))
end))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let uu____1573 = (translate_expr s1 var [] env true)
in (match (uu____1573) with
| (r1, env1) -> begin
(

let s1 = FStar_Extraction_JavaScript_Ast.JSS_Block (r1)
in (

let uu____1585 = (match (s2) with
| Some (v) -> begin
(

let uu____1593 = (translate_expr v var [] env true)
in (match (uu____1593) with
| (r2, env2) -> begin
((Some (FStar_Extraction_JavaScript_Ast.JSS_Block (r2))), (env2))
end))
end
| None -> begin
((None), (env))
end)
in (match (uu____1585) with
| (s2, env2) -> begin
(

let uu____1613 = (

let uu____1617 = (is_pure_expr cond var)
in (match (uu____1617) with
| true -> begin
(

let uu____1622 = (translate_expr_pure cond env)
in (match (uu____1622) with
| (c1, envc) -> begin
(((FStar_Extraction_JavaScript_Ast.JSS_If (((c1), (s1), (s2))))::[]), (envc))
end))
end
| uu____1632 -> begin
(

let uu____1633 = (translate_expr cond (("_cond"), (None)) ((FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (None)))), (s1), (s2))))::[]) env true)
in (match (uu____1633) with
| (c1, envc) -> begin
(((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) c1)), (envc))
end))
end))
in (match (uu____1613) with
| (c, env) -> begin
(

let uu____1660 = (match (isDecl) with
| true -> begin
((c), (env))
end
| uu____1668 -> begin
(

let env = (extendEnv env (([]), ((Prims.fst var))) None)
in (((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) c)), (env)))
end)
in (match (uu____1660) with
| (c, env) -> begin
(

let env = (

let uu___152_1687 = env
in {names = uu___152_1687.names; module_name = uu___152_1687.module_name; import_module_names = (FStar_List.append env.import_module_names (FStar_List.append env1.import_module_names env2.import_module_names))})
in (((FStar_List.append c lstmt)), (env)))
end))
end))
end)))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (uu____1689) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (uu____1696) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t, uu____1709) -> begin
(

let lp_generic = (match ((Prims.snd var)) with
| None -> begin
None
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (uu____1720, uu____1721, lp) -> begin
lp
end
| uu____1739 -> begin
None
end)
end)
in (

let uu____1741 = (translate_type t lp_generic env)
in (match (uu____1741) with
| (t, env) -> begin
(

let var = (((Prims.fst var)), (Some (t)))
in (translate_expr in_e var lstmt env isDecl))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let match_e = (let _0_393 = (Prims.fst (FStar_Extraction_ML_Syntax.gensym ()))
in ((_0_393), (None)))
in (

let uu____1772 = (

let uu____1776 = (is_pure_expr e_in var)
in (match (uu____1776) with
| true -> begin
(

let uu____1781 = (translate_expr_pure e_in env)
in (match (uu____1781) with
| (r1, env) -> begin
(

let uu____1789 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (match_e)) var env)
in (match (uu____1789) with
| (r2, env2) -> begin
(

let env = (

let uu___153_1798 = env
in {names = uu___153_1798.names; module_name = uu___153_1798.module_name; import_module_names = (FStar_List.append env.import_module_names env2.import_module_names)})
in (((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (match_e)), (Some (r1)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::(r2)::[]), (env)))
end))
end))
end
| uu____1804 -> begin
(

let uu____1805 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (match_e)) var env)
in (match (uu____1805) with
| (r2, env2) -> begin
(

let uu____1813 = (translate_expr e_in match_e ((r2)::[]) env true)
in (match (uu____1813) with
| (r1, env) -> begin
(

let env = (

let uu___154_1825 = env
in {names = uu___154_1825.names; module_name = uu___154_1825.module_name; import_module_names = (FStar_List.append env.import_module_names env2.import_module_names)})
in (((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (match_e)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) r1)), (env)))
end))
end))
end))
in (match (uu____1772) with
| (c, env) -> begin
(

let c = (FStar_Extraction_JavaScript_Ast.JSS_Block (c))::[]
in (

let uu____1840 = (match (isDecl) with
| true -> begin
((c), (env))
end
| uu____1848 -> begin
(

let env = (extendEnv env (([]), ((Prims.fst var))) None)
in (((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) c)), (env)))
end)
in (match (uu____1840) with
| (c, env) -> begin
(((FStar_List.append c lstmt)), (env))
end)))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(

let rec translate_seq = (fun l env acc -> (match (l) with
| [] -> begin
(failwith "Empty list in [MLE_Seq]")
end
| (x)::[] -> begin
(

let uu____1893 = (translate_expr x var [] env isDecl)
in (match (uu____1893) with
| (r, env) -> begin
(((FStar_List.append acc r)), (env))
end))
end
| (hd)::tl -> begin
(

let uu____1908 = (translate_expr hd (("_"), (None)) [] env true)
in (match (uu____1908) with
| (r, e1) -> begin
(translate_seq tl e1 (FStar_List.append acc r))
end))
end))
in (

let uu____1920 = (translate_seq ls env [])
in (match (uu____1920) with
| (r, env) -> begin
(((FStar_List.append r lstmt)), (env))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let uu____1936 = (create_pure_args args var env)
in (match (uu____1936) with
| (args, new_fv, env) -> begin
(

let uu____1952 = (translate_arg_app e args var env)
in (match (uu____1952) with
| (expr, env) -> begin
(get_res expr new_fv env)
end))
end))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(

let uu____1970 = (create_pure_args lexpr var env)
in (match (uu____1970) with
| (lexpr, new_fv, env) -> begin
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
| uu____1999 -> begin
FStar_Extraction_JavaScript_Ast.JSE_Object ((let _0_397 = (FStar_List.mapi (fun i x -> FStar_Extraction_JavaScript_Ast.JSPO_Property ((let _0_396 = FStar_Extraction_JavaScript_Ast.JSO_Identifier ((let _0_395 = (let _0_394 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_394))
in ((_0_395), (None))))
in ((_0_396), (x), (FStar_Extraction_JavaScript_Ast.JSO_Init))))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _0_397)))
end)
in (get_res expr new_fv env))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let uu____2014 = (FStar_List.fold_left (fun uu____2027 uu____2028 -> (match (((uu____2027), (uu____2028))) with
| ((lexpr, lnew_fv, e), (id, x)) -> begin
(

let uu____2064 = (create_pure_args ((x)::[]) var e)
in (match (uu____2064) with
| (expr, fv, e1) -> begin
(let _0_401 = (let _0_400 = (let _0_399 = FStar_Extraction_JavaScript_Ast.JSPO_Property ((let _0_398 = (FStar_List.nth expr (Prims.parse_int "0"))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_0_398), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in (_0_399)::[])
in (FStar_List.append lexpr _0_400))
in ((_0_401), ((FStar_List.append fv lnew_fv)), (e1)))
end))
end)) (([]), ([]), (env)) fields)
in (match (uu____2014) with
| (create_fields, new_fv, env) -> begin
(

let expr = FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))
in (get_res expr new_fv env))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let uu____2101 = (FStar_List.fold_left (fun uu____2112 x -> (match (uu____2112) with
| (lexpr, lnew_fv, e) -> begin
(

let uu____2131 = (create_pure_args ((x)::[]) var e)
in (match (uu____2131) with
| (expr, fv, e1) -> begin
(((FStar_List.append lexpr expr)), ((FStar_List.append fv lnew_fv)), (e1))
end))
end)) (([]), ([]), (env)) lexp)
in (match (uu____2101) with
| (create_fields, new_fv, env) -> begin
(

let expr = FStar_Extraction_JavaScript_Ast.JSE_Array (Some (create_fields))
in (get_res expr new_fv env))
end))
end
| uu____2165 -> begin
(failwith "todo: translation ml-expr")
end)))
and create_pure_args : FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  env_t  ->  (FStar_Extraction_JavaScript_Ast.expression_t Prims.list * FStar_Extraction_JavaScript_Ast.statement_t Prims.list * env_t) = (fun args var env -> (FStar_List.fold_left (fun uu____2181 x -> (match (uu____2181) with
| (lexpr, lnew_fv, e) -> begin
(match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), uu____2207) when ((c = "Nil") || (c = "None")) -> begin
(

let uu____2215 = (translate_expr_pure x e)
in (match (uu____2215) with
| (r1, e1) -> begin
(

let uu____2225 = (translate_type x.FStar_Extraction_ML_Syntax.mlty None e1)
in (match (uu____2225) with
| (t1, e1) -> begin
(((FStar_List.append lexpr ((FStar_Extraction_JavaScript_Ast.JSE_TypeCast (((r1), (t1))))::[]))), (lnew_fv), (e1))
end))
end))
end
| uu____2238 -> begin
(

let uu____2239 = (is_pure_expr x var)
in (match (uu____2239) with
| true -> begin
(

let uu____2246 = (translate_expr_pure x e)
in (match (uu____2246) with
| (r1, e1) -> begin
(((FStar_List.append lexpr ((r1)::[]))), (lnew_fv), (e1))
end))
end
| uu____2258 -> begin
(

let fv_x = (Prims.fst (FStar_Extraction_ML_Syntax.gensym ()))
in (

let uu____2260 = (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (uu____2267) -> begin
(

let uu____2268 = (translate_expr_pure x e)
in (match (uu____2268) with
| (r1, e1) -> begin
(((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (Some (r1)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::[]), (e1))
end))
end
| uu____2282 -> begin
(translate_expr x ((fv_x), (None)) [] env false)
end)
in (match (uu____2260) with
| (c, e1) -> begin
(((FStar_List.append lexpr ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None))))::[]))), ((FStar_List.append c lnew_fv)), (e1))
end)))
end))
end)
end)) (([]), ([]), (env)) args))
and translate_arg_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list  ->  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  env_t  ->  (FStar_Extraction_JavaScript_Ast.expression_t * env_t) = (fun e args var env -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _0_405 = FStar_Extraction_JavaScript_Ast.JSE_Binary ((let _0_404 = (FStar_Util.must (mk_op_bin op))
in (let _0_403 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _0_402 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_0_404), (_0_403), (_0_402))))))
in ((_0_405), (env)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _0_409 = FStar_Extraction_JavaScript_Ast.JSE_Logical ((let _0_408 = (FStar_Util.must (mk_op_bool op))
in (let _0_407 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _0_406 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_0_408), (_0_407), (_0_406))))))
in ((_0_409), (env)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _0_412 = FStar_Extraction_JavaScript_Ast.JSE_Unary ((let _0_411 = (FStar_Util.must (mk_op_un op))
in (let _0_410 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_0_411), (_0_410)))))
in ((_0_412), (env)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((let _0_413 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_413 = "FStar.Buffer.op_Array_Access")) || (let _0_414 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_414 = "FStar.Buffer.index"))) -> begin
(let _0_417 = FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_416 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _0_415 = FStar_Extraction_JavaScript_Ast.JSPM_Expression ((FStar_List.nth args (Prims.parse_int "1")))
in ((_0_416), (_0_415)))))
in ((_0_417), (env)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((let _0_418 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_418 = "FStar.Buffer.op_Array_Assignment")) || (let _0_419 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_419 = "FStar.Buffer.upd"))) -> begin
(let _0_424 = FStar_Extraction_JavaScript_Ast.JSE_Assignment ((let _0_423 = FStar_Extraction_JavaScript_Ast.JGP_Expression (FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_421 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _0_420 = FStar_Extraction_JavaScript_Ast.JSPM_Expression ((FStar_List.nth args (Prims.parse_int "1")))
in ((_0_421), (_0_420))))))
in (let _0_422 = (FStar_List.nth args (Prims.parse_int "2"))
in ((_0_423), (_0_422)))))
in ((_0_424), (env)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((let _0_425 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_425 = "FStar.ST.op_Bang")) || (let _0_426 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_426 = "FStar.ST.read"))) -> begin
(let _0_428 = FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_427 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_0_427), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0"))))))))
in ((_0_428), (env)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((let _0_429 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_429 = "FStar.ST.op_Colon_Equals")) || (let _0_430 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_430 = "FStar.ST.write"))) -> begin
(

let expr = FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_431 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_0_431), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0"))))))))
in (let _0_433 = FStar_Extraction_JavaScript_Ast.JSE_Assignment ((let _0_432 = (FStar_List.nth args (Prims.parse_int "1"))
in ((FStar_Extraction_JavaScript_Ast.JGP_Expression (expr)), (_0_432))))
in ((_0_433), (env))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (let _0_434 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_434 = "FStar.ST.alloc")) -> begin
(let _0_436 = FStar_Extraction_JavaScript_Ast.JSE_Array (Some ((let _0_435 = (FStar_List.nth args (Prims.parse_int "0"))
in (_0_435)::[])))
in ((_0_436), (env)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(

let uu____2327 = (addImportModule env ((path), (function_name)))
in (match (uu____2327) with
| (name, env) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))), (env))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____2338) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))), (env))
end
| uu____2341 -> begin
(

let uu____2342 = (is_pure_expr e var)
in (match (uu____2342) with
| true -> begin
(

let uu____2346 = (translate_expr_pure e env)
in (match (uu____2346) with
| (r, env) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Call (((r), (args)))), (env))
end))
end
| uu____2354 -> begin
(failwith "todo: translation [MLE_App]")
end))
end))
and map_expr_pure : FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  env_t  ->  (FStar_Extraction_JavaScript_Ast.expression_t Prims.list * env_t) = (fun exprs env -> (FStar_List.fold_left (fun uu____2363 x -> (match (uu____2363) with
| (r, e) -> begin
(

let uu____2375 = (translate_expr_pure x e)
in (match (uu____2375) with
| (r1, e1) -> begin
(((FStar_List.append r ((r1)::[]))), (e1))
end))
end)) (([]), (env)) exprs))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  env_t  ->  (FStar_Extraction_JavaScript_Ast.expression_t * env_t) = (fun e env -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _0_437 = (translate_constant c)
in ((_0_437), (env)))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, uu____2393) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (env))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, name) -> begin
(

let uu____2399 = (addImportModule env ((path), (name)))
in (match (uu____2399) with
| (name, env) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (env))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let uu____2410 = (map_expr_pure lexp env)
in (match (uu____2410) with
| (r, env) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Array (Some (r))), (env))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let uu____2431 = (FStar_List.fold_left (fun uu____2440 uu____2441 -> (match (((uu____2440), (uu____2441))) with
| ((r, e), (id, x)) -> begin
(

let uu____2466 = (translate_expr_pure x e)
in (match (uu____2466) with
| (r1, e1) -> begin
(((FStar_List.append r ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (r1), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]))), (e1))
end))
end)) (([]), (env)) fields)
in (match (uu____2431) with
| (create_fields, env) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))), (env))
end))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(

let uu____2494 = (addImportModule env ((path), (c)))
in (match (uu____2494) with
| (name, env) -> begin
(match (c) with
| x when ((x = "Cons") || (x = "Nil")) -> begin
(match (lexpr) with
| [] -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Array (None)), (env))
end
| (hd)::tl -> begin
(

let uu____2511 = (translate_expr_pure hd env)
in (match (uu____2511) with
| (r1, e1) -> begin
(

let uu____2518 = (map_expr_pure tl e1)
in (match (uu____2518) with
| (r2, e2) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Array (Some ((r1)::[]))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("concat"), (None))))))), (r2)))), (env))
end))
end))
end)
end
| x when ((x = "Some") || (x = "None")) -> begin
(match (lexpr) with
| [] -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))), (env))
end
| (hd)::tl -> begin
(

let uu____2537 = (map_expr_pure lexpr env)
in (match (uu____2537) with
| (r1, e1) -> begin
(let _0_438 = (FStar_List.nth r1 (Prims.parse_int "0"))
in ((_0_438), (e1)))
end))
end)
end
| uu____2547 -> begin
(

let uu____2548 = (FStar_List.fold_left (fun uu____2557 x -> (match (uu____2557) with
| (i, r, e) -> begin
(

let uu____2572 = (translate_expr_pure x e)
in (match (uu____2572) with
| (r1, e1) -> begin
(let _0_444 = (let _0_443 = (let _0_442 = FStar_Extraction_JavaScript_Ast.JSPO_Property ((let _0_441 = FStar_Extraction_JavaScript_Ast.JSO_Identifier ((let _0_440 = (let _0_439 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_439))
in ((_0_440), (None))))
in ((_0_441), (r1), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in (_0_442)::[])
in (FStar_List.append r _0_443))
in (((i + (Prims.parse_int "1"))), (_0_444), (e1)))
end))
end)) (((Prims.parse_int "0")), ([]), (env)) lexpr)
in (match (uu____2548) with
| (uu____2586, r, env) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (name)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) r))), (env))
end))
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, uu____2593, uu____2594) -> begin
(translate_expr_pure e env)
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let uu____2599 = (FStar_List.fold_left (fun uu____2606 x -> (match (uu____2606) with
| (r, e) -> begin
(match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), uu____2623) when ((c = "Nil") || (c = "None")) -> begin
(

let uu____2631 = (translate_expr_pure x e)
in (match (uu____2631) with
| (r1, e1) -> begin
(

let uu____2639 = (translate_type x.FStar_Extraction_ML_Syntax.mlty None e1)
in (match (uu____2639) with
| (r2, e2) -> begin
(((FStar_List.append r ((FStar_Extraction_JavaScript_Ast.JSE_TypeCast (((r1), (r2))))::[]))), (e2))
end))
end))
end
| uu____2649 -> begin
(

let uu____2650 = (translate_expr_pure x e)
in (match (uu____2650) with
| (r1, e1) -> begin
(((FStar_List.append r ((r1)::[]))), (e1))
end))
end)
end)) (([]), (env)) args)
in (match (uu____2599) with
| (args, env) -> begin
(translate_arg_app e args ((""), (None)) env)
end))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, (path, name)) -> begin
(

let uu____2675 = (translate_expr_pure expr env)
in (match (uu____2675) with
| (r, env) -> begin
(

let uu____2682 = (addImportModule env ((path), (name)))
in (match (uu____2682) with
| (name, env) -> begin
((FStar_Extraction_JavaScript_Ast.JSE_Member (((r), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" name)), (None))))))), (env))
end))
end))
end
| uu____2691 -> begin
(failwith "todo: translation ml-expr-pure")
end))
and translate_match : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  env_t  ->  (FStar_Extraction_JavaScript_Ast.statement_t * env_t) = (fun lb match_e var env -> (match (lb) with
| [] -> begin
((FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))), (env))
end
| ((p, guard, expr_r))::tl -> begin
(

let uu____2729 = (

let uu____2732 = (is_pure_expr expr_r var)
in (match (uu____2732) with
| true -> begin
(

let uu____2736 = (translate_expr_pure expr_r env)
in (match (uu____2736) with
| (r1, e1) -> begin
((FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (r1))))), (e1))
end))
end
| uu____2743 -> begin
(

let uu____2744 = (translate_expr expr_r var [] env true)
in (match (uu____2744) with
| (r1, e1) -> begin
((FStar_Extraction_JavaScript_Ast.JSS_Seq (r1)), (e1))
end))
end))
in (match (uu____2729) with
| (expr_t, env1) -> begin
(let _0_445 = (translate_match tl match_e var env)
in (translate_pat_guard ((p), (guard)) match_e expr_t _0_445 env1))
end))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  (FStar_Extraction_JavaScript_Ast.statement_t * env_t)  ->  env_t  ->  (FStar_Extraction_JavaScript_Ast.statement_t * env_t) = (fun uu____2759 match_e s1 s2 env -> (match (uu____2759) with
| (p, guard) -> begin
(

let uu____2777 = s2
in (match (uu____2777) with
| (s2, env2) -> begin
(

let uu____2784 = (match (guard) with
| None -> begin
(translate_pat p match_e s1 s2 env)
end
| Some (v_guard) -> begin
(

let uu____2790 = (translate_expr_pure v_guard env)
in (match (uu____2790) with
| (r, env1) -> begin
(

let cond_stmt = FStar_Extraction_JavaScript_Ast.JSS_If (((r), (s1), (Some (s2))))
in (translate_pat p match_e cond_stmt s2 env1))
end))
end)
in (match (uu____2784) with
| (stmt, env) -> begin
(

let env = (

let uu___155_2804 = env
in {names = uu___155_2804.names; module_name = uu___155_2804.module_name; import_module_names = (FStar_List.append env.import_module_names env2.import_module_names)})
in ((stmt), (env)))
end))
end))
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  env_t  ->  (FStar_Extraction_JavaScript_Ast.statement_t * env_t) = (fun p match_e s1 s2 env -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, uu____2815) -> begin
((FStar_Extraction_JavaScript_Ast.JSS_Seq ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (match_e)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::(s1)::[])), (env))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
((s1), (env))
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _0_448 = FStar_Extraction_JavaScript_Ast.JSS_If ((let _0_447 = FStar_Extraction_JavaScript_Ast.JSE_Binary ((let _0_446 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (match_e), (_0_446))))
in ((_0_447), (s1), (Some (s2)))))
in ((_0_448), (env)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((path, c), lp) -> begin
(

let uu____2833 = (addImportModule env ((path), (c)))
in (match (uu____2833) with
| (name, env) -> begin
(

let rec translate_p_ctor = (fun lp match_e s1 s2 i env -> (

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
| uu____2869 -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_451 = FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((let _0_450 = (let _0_449 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_449))
in ((_0_450), (None))))
in ((match_e), (_0_451))))
end)
in (match (lp) with
| [] -> begin
((s1), (env))
end
| (x)::[] -> begin
(

let uu____2874 = (translate_pat x new_fv_x s1 s2 env)
in (match (uu____2874) with
| (r, e1) -> begin
((r), (e1))
end))
end
| (hd)::tl -> begin
(

let uu____2884 = (translate_p_ctor tl match_e s1 s2 (i + (Prims.parse_int "1")) env)
in (match (uu____2884) with
| (r, e1) -> begin
(translate_pat hd new_fv_x r s2 e1)
end))
end)))
in (

let if_stmt = (fun if_cond -> (

let uu____2897 = (translate_p_ctor lp match_e s1 s2 (Prims.parse_int "0") env)
in (match (uu____2897) with
| (r, e1) -> begin
((FStar_Extraction_JavaScript_Ast.JSS_If (((if_cond), (r), (Some (s2))))), (e1))
end)))
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
| uu____2913 -> begin
(

let isSimple = (match (match_e) with
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (uu____2915) -> begin
true
end
| uu____2919 -> begin
false
end)
in (match (isSimple) with
| true -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((match_e), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))))
end
| uu____2923 -> begin
(

let new_name = (Prims.fst (FStar_Extraction_ML_Syntax.gensym ()))
in (

let if_cond = FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))
in (

let uu____2928 = (translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))) s1 s2 (Prims.parse_int "0") env)
in (match (uu____2928) with
| (r, env1) -> begin
((FStar_Extraction_JavaScript_Ast.JSS_Seq ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((new_name), (None)))), (Some (match_e)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::(FStar_Extraction_JavaScript_Ast.JSS_If (((if_cond), (r), (Some (s2)))))::[])), (env1))
end))))
end))
end)))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (lp) -> begin
(

let rec translate_p_branch = (fun lp match_e s1 s2 env -> (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_branch")
end
| (x)::[] -> begin
(translate_pat x match_e s1 s2 env)
end
| (hd)::tl -> begin
(

let uu____2972 = (translate_p_branch tl match_e s1 s2 env)
in (match (uu____2972) with
| (r, e1) -> begin
(translate_pat hd match_e s1 r e1)
end))
end))
in (translate_p_branch lp match_e s1 s2 env))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, lp) -> begin
(

let rec translate_p_record = (fun lp match_e s1 s2 env -> (

let new_fv_x = (fun n -> FStar_Extraction_JavaScript_Ast.JSE_Member (((match_e), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" n)), (None)))))))
in (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_record")
end
| (x)::[] -> begin
(translate_pat (Prims.snd x) (new_fv_x (Prims.fst x)) s1 s2 env)
end
| (hd)::tl -> begin
(

let uu____3040 = (translate_p_record tl match_e s1 s2 env)
in (match (uu____3040) with
| (r, e1) -> begin
(translate_pat (Prims.snd hd) (new_fv_x (Prims.fst hd)) r s2 e1)
end))
end)))
in (translate_p_record lp match_e s1 s2 env))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(

let rec translate_p_tuple = (fun lp d match_e s1 s2 env -> (

let new_fv_x = FStar_Extraction_JavaScript_Ast.JSE_Member ((let _0_453 = FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal ((let _0_452 = (FStar_Util.string_of_int d)
in ((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int d))), (_0_452)))))
in ((match_e), (_0_453))))
in (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_tuple")
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2 env)
end
| (hd)::tl -> begin
(

let uu____3081 = (translate_p_tuple tl (d + (Prims.parse_int "1")) match_e s1 s2 env)
in (match (uu____3081) with
| (r, e1) -> begin
(translate_pat hd new_fv_x r s2 e1)
end))
end)))
in (translate_p_tuple lp (Prims.parse_int "0") match_e s1 s2 env))
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, uu____3091) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (uu____3099) -> begin
(failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (uu____3101) -> begin
(failwith "todo: translate_const [MLC_Bytes]")
end))
and map_type : env_t  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlsymbol Prims.list Prims.option  ->  (FStar_Extraction_JavaScript_Ast.typ Prims.list * env_t) = (fun env args lp_generic -> (FStar_List.fold_left (fun uu____3112 x -> (match (uu____3112) with
| (r, e) -> begin
(

let uu____3124 = (translate_type x lp_generic e)
in (match (uu____3124) with
| (r1, e1) -> begin
(((FStar_List.append r ((r1)::[]))), (e1))
end))
end)) (([]), (env)) args))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlsymbol Prims.list Prims.option  ->  env_t  ->  (FStar_Extraction_JavaScript_Ast.typ * env_t) = (fun t lp_generic env -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Any), (env))
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, uu____3144) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Generic (((id), (None)))), (env))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(

let uu____3150 = (map_type env lt lp_generic)
in (match (uu____3150) with
| (r, env) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Tuple (r)), (env))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, e_tag, t2) -> begin
(

let uu____3163 = (translate_type t1 None env)
in (match (uu____3163) with
| (t1, env) -> begin
(

let uu____3171 = (match ((e_tag = FStar_Extraction_ML_Syntax.E_GHOST)) with
| true -> begin
((FStar_Extraction_JavaScript_Ast.JST_Null), (env))
end
| uu____3176 -> begin
(translate_type t2 None env)
end)
in (match (uu____3171) with
| (t2, env) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Function (((((((("_1"), (None))), (t1)))::[]), (t2), (lp_generic)))), (env))
end))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) when (let _0_454 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_454 = "FStar.ST.ref")) -> begin
(

let uu____3208 = (let _0_455 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_type _0_455 lp_generic env))
in (match (uu____3208) with
| (r, env) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Array (r)), (env))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____3215, p) when (let _0_456 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_456 = "FStar.Buffer.buffer")) -> begin
(

let uu____3219 = (addImportModule env p)
in (match (uu____3219) with
| (name, env) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Generic (((name), (None)))), (env))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____3229, p) when (let _0_457 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_457 = "FStar.Ghost.erased")) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Any), (env))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
(match ((is_standart_type name)) with
| true -> begin
(let _0_458 = (FStar_Util.must (mk_standart_type name))
in ((_0_458), (env)))
end
| uu____3245 -> begin
(match ((FStar_Option.isSome (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name))))) with
| true -> begin
(

let uu____3249 = (map_type env args lp_generic)
in (match (uu____3249) with
| (r, env) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Tuple (r)), (env))
end))
end
| uu____3259 -> begin
(

let uu____3260 = (match (args) with
| [] -> begin
((None), (env))
end
| uu____3272 -> begin
(

let uu____3274 = (map_type env args lp_generic)
in (match (uu____3274) with
| (r, env) -> begin
((Some (r)), (env))
end))
end)
in (match (uu____3260) with
| (args_t, env) -> begin
(

let uu____3297 = (addImportModule env ((path), (name)))
in (match (uu____3297) with
| (name, env) -> begin
((FStar_Extraction_JavaScript_Ast.JST_Generic (((name), (args_t)))), (env))
end))
end))
end)
end)
end))




