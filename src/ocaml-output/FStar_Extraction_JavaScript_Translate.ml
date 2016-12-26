
open Prims

type file =
(Prims.string * FStar_Extraction_JavaScript_Ast.t)


type env =
{names : name Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; module_name = module_name})


let mk_op_bin : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_bin Prims.option = (fun _84_1 -> (match (_84_1) with
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
| _84_25 -> begin
None
end))


let is_op_bin : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bin op) <> None))


let mk_op_un : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_un Prims.option = (fun _84_2 -> (match (_84_2) with
| "op_Negation" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSU_Not)
end
| "op_Minus" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSU_Minus)
end
| _84_31 -> begin
None
end))


let is_op_un : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_un op) <> None))


let mk_op_bool : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_log Prims.option = (fun _84_3 -> (match (_84_3) with
| "op_AmpAmp" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_And)
end
| "op_BarBar" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_Or)
end
| _84_37 -> begin
None
end))


let is_op_bool : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bool op) <> None))


let mk_standart_type : Prims.string  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option = (fun _84_4 -> (match (_84_4) with
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
| _84_46 -> begin
None
end))


let is_standart_type : Prims.string  ->  Prims.bool = (fun t -> ((mk_standart_type t) <> None))


let float_of_int : Prims.int  ->  FStar_BaseTypes.float = (fun i -> (FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)))


let export_modules : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let current_module_name : Prims.string FStar_ST.ref = (FStar_ST.alloc "")


let lp_generic : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let isEqVar : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let getName = (fun _84_51 -> (match (_84_51) with
| (path, n) -> begin
(

let path = (FStar_String.concat "_" path)
in if ((path = (FStar_ST.read current_module_name)) || (path = "")) then begin
((n), (None))
end else begin
(

let _84_54 = if (not ((let _184_37 = (FStar_ST.read export_modules)
in (FStar_List.existsb (fun x -> (x = path)) _184_37)))) then begin
(let _184_39 = (let _184_38 = (FStar_ST.read export_modules)
in (FStar_List.append ((path)::[]) _184_38))
in (FStar_ST.op_Colon_Equals export_modules _184_39))
end else begin
()
end
in (((Prims.strcat path (Prims.strcat "." n))), (None)))
end)
end))


let rec is_pure_expr = (fun e var -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (n, _84_66) -> begin
(n <> (Prims.fst var))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, _84_71) -> begin
(is_pure_expr expr var)
end
| FStar_Extraction_ML_Syntax.MLE_CTor (p, le) -> begin
(not ((let _184_43 = (FStar_List.map (fun x -> (is_pure_expr x var)) le)
in (FStar_List.contains false _184_43))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (le) -> begin
(not ((let _184_45 = (FStar_List.map (fun x -> (is_pure_expr x var)) le)
in (FStar_List.contains false _184_45))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_84_83, lne) -> begin
(not ((let _184_47 = (FStar_List.map (fun _84_89 -> (match (_84_89) with
| (n, e) -> begin
(is_pure_expr e var)
end)) lne)
in (FStar_List.contains false _184_47))))
end
| FStar_Extraction_ML_Syntax.MLE_App (_84_91, args) -> begin
(not ((let _184_49 = (FStar_List.map (fun x -> (is_pure_expr x var)) args)
in (FStar_List.contains false _184_49))))
end
| _84_97 -> begin
false
end))


let isMutable = (fun tys -> (match (tys) with
| None -> begin
false
end
| Some (_84_101, ty) -> begin
(match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_84_106, p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.ref") -> begin
true
end
| _84_111 -> begin
false
end)
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _84_113 -> (match (_84_113) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _84_122 = m
in (match (_84_122) with
| ((prefix, final), _84_119, _84_121) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _84_132 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (

let _84_134 = (FStar_ST.op_Colon_Equals export_modules [])
in (let _184_85 = (translate_module m)
in Some (_184_85))))
end)
with
| e -> begin
(

let _84_128 = (let _184_87 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _184_87))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _84_140 -> (match (_84_140) with
| (module_name, modul, _84_139) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let _84_146 = (FStar_ST.op_Colon_Equals current_module_name (FStar_String.concat "_" module_name))
in (

let res = (FStar_List.filter_map translate_decl decls)
in (

let create_module_imports = (let _184_94 = (let _184_92 = (let _184_90 = (FStar_ST.read export_modules)
in (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (((m), (None)))) _184_90))
in (FStar_All.pipe_right _184_92 (fun _184_91 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_184_91))))
in (FStar_All.pipe_right _184_94 (fun _184_93 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_184_93))))
in (FStar_List.append ((create_module_imports)::[]) res))))
end
| _84_152 -> begin
(failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (_84_156, c_flag, lfunc) -> begin
(

let for1 = (fun _84_170 -> (match (_84_170) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, _84_168); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = (

let _84_171 = (FStar_ST.op_Colon_Equals lp_generic [])
in if ((not (pt)) || unit_b) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some (lp, ty) -> begin
(

let _84_182 = (let _184_99 = (FStar_List.map (fun _84_181 -> (match (_84_181) with
| (id, _84_180) -> begin
id
end)) lp)
in (FStar_ST.op_Colon_Equals lp_generic _184_99))
in (let _184_101 = (translate_type ty)
in (FStar_All.pipe_right _184_101 (fun _184_100 -> Some (_184_100)))))
end)
end)
in (

let is_private = (FStar_List.contains FStar_Extraction_ML_Syntax.Private c_flag)
in (

let c = if (is_pure_expr expr ((name), (None))) then begin
(

let var_decl_q = if (isMutable tys) then begin
FStar_Extraction_JavaScript_Ast.JSV_Let
end else begin
FStar_Extraction_JavaScript_Ast.JSV_Const
end
in (let _184_106 = (let _184_105 = (let _184_104 = (let _184_103 = (let _184_102 = (translate_expr_pure expr)
in Some (_184_102))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (_184_103)))
in ((_184_104), (var_decl_q)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_184_105))
in (_184_106)::[]))
end else begin
(let _184_107 = (FStar_ST.alloc [])
in (translate_expr expr ((name), (t)) None false _184_107 (isMutable tys)))
end
in if is_private then begin
c
end else begin
(FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (FStar_Extraction_JavaScript_Ast.JSS_Block (c))), (FStar_Extraction_JavaScript_Ast.ExportValue))))::[]
end)))
end))
in (let _184_113 = (let _184_111 = (let _184_109 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _184_109 (fun _184_108 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_184_108))))
in (FStar_All.pipe_right _184_111 (fun _184_110 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_184_110))))
in (FStar_All.pipe_right _184_113 (fun _184_112 -> Some (_184_112)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_84_189) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_84_192, name, _84_195, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| _84_203 -> begin
(let _184_116 = (FStar_List.map (fun _84_207 -> (match (_84_207) with
| (id, _84_206) -> begin
id
end)) tparams)
in (FStar_All.pipe_right _184_116 (fun _184_115 -> Some (_184_115))))
end)
in (

let forbody = (fun body -> (

let get_export = (fun stmt -> (FStar_All.pipe_right ((FStar_Extraction_JavaScript_Ast.JSE_Declaration (stmt)), (FStar_Extraction_JavaScript_Ast.ExportType)) (fun _184_121 -> FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (_184_121))))
in (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _184_124 = (let _184_123 = (let _184_122 = (translate_type t)
in ((((name), (None))), (tparams), (_184_122)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_184_123))
in (get_export _184_124))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _84_220 -> (match (_84_220) with
| (n, t) -> begin
(let _184_126 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_184_126)))
end)) fields)
in (get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.mapi (fun i t -> (let _184_137 = (let _184_135 = (let _184_134 = (let _184_133 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _184_133))
in ((_184_134), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_184_135))
in (let _184_136 = (translate_type t)
in ((_184_137), (_184_136))))) fields))
in (

let lfields_t = (FStar_List.map (fun _84_232 -> (match (_84_232) with
| (n, l) -> begin
(let _184_144 = (let _184_143 = (let _184_142 = (let _184_141 = (let _184_140 = (let _184_139 = (fields_t l)
in (FStar_List.append (tag n) _184_139))
in ((_184_140), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_184_141))
in ((((n), (None))), (tparams), (_184_142)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_184_143))
in (get_export _184_144))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _184_147 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((x), (None)))), (None)))) t)
in (FStar_All.pipe_right _184_147 (fun _184_146 -> Some (_184_146))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun _84_241 -> (match (_84_241) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((n), (None)))), (tparams_gen)))
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
in (let _184_151 = (FStar_All.pipe_right body_t (fun _184_149 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_184_149)))
in (FStar_All.pipe_right _184_151 (fun _184_150 -> Some (_184_150)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_84_249) -> begin
(failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_84_252) -> begin
(failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _184_154 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block ([])) (fun _184_152 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_184_152)))
in (FStar_All.pipe_right _184_154 (fun _184_153 -> Some (_184_153))))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_84_259) -> begin
(failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.list Prims.option  ->  Prims.bool  ->  Prims.string Prims.list FStar_ST.ref  ->  Prims.bool  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.list = (fun e var lstmt isDecl lDecl isMutableV -> (

let get_res = (fun expr new_fv -> (

let lstmt = (match (lstmt) with
| Some (v) -> begin
v
end
| None -> begin
[]
end)
in (

let isAssgmnt = (FStar_ST.alloc [])
in (

let expr = (match (expr) with
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (_84_276) -> begin
(

let _84_278 = (FStar_ST.op_Colon_Equals isAssgmnt ((FStar_Extraction_JavaScript_Ast.JSS_Expression (expr))::[]))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))
end
| _84_281 -> begin
expr
end)
in (

let expr = if isDecl then begin
FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (expr))))
end else begin
(

let _84_283 = (let _184_166 = (let _184_165 = (FStar_ST.read lDecl)
in (FStar_List.append (((Prims.fst var))::[]) _184_165))
in (FStar_ST.op_Colon_Equals lDecl _184_166))
in (

let var_decl_q = if isMutableV then begin
FStar_Extraction_JavaScript_Ast.JSV_Let
end else begin
FStar_Extraction_JavaScript_Ast.JSV_Const
end
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (expr)))), (var_decl_q)))))
end
in (match (new_fv) with
| Some (v) -> begin
if (FStar_ST.read isEqVar) then begin
(

let _84_289 = (FStar_ST.op_Colon_Equals isEqVar false)
in (let _184_169 = (FStar_ST.read v)
in (let _184_168 = (let _184_167 = (FStar_ST.read isAssgmnt)
in (FStar_List.append _184_167 ((FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append ((expr)::[]) lstmt)))::[])))
in (FStar_List.append _184_169 _184_168))))
end else begin
(let _184_172 = (FStar_ST.read v)
in (let _184_171 = (let _184_170 = (FStar_ST.read isAssgmnt)
in (FStar_List.append _184_170 (FStar_List.append ((expr)::[]) lstmt)))
in (FStar_List.append _184_172 _184_171)))
end
end
| None -> begin
(let _184_173 = (FStar_ST.read isAssgmnt)
in (FStar_List.append _184_173 (FStar_List.append ((expr)::[]) lstmt)))
end))))))
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e var) -> begin
(

let expr = (translate_expr_pure e)
in (get_res expr None))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((_84_295, _84_297, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _84_304); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let isEqName = (let _184_175 = (FStar_ST.read lDecl)
in (FStar_List.existsb (fun x -> (x = name)) _184_175))
in (

let lDecl = if isEqName then begin
lDecl
end else begin
(

let _84_314 = (let _184_177 = (let _184_176 = (FStar_ST.read lDecl)
in (FStar_List.append ((name)::[]) _184_176))
in (FStar_ST.op_Colon_Equals lDecl _184_177))
in lDecl)
end
in (

let c = (translate_expr continuation var lstmt isDecl lDecl isMutableV)
in if (is_pure_expr body ((name), (None))) then begin
(

let var_decl_q = if (isMutable tys) then begin
FStar_Extraction_JavaScript_Ast.JSV_Let
end else begin
FStar_Extraction_JavaScript_Ast.JSV_Const
end
in (

let c = (let _184_183 = (let _184_182 = (let _184_181 = (let _184_180 = (let _184_179 = (let _184_178 = (translate_expr_pure body)
in Some (_184_178))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (_184_179)))
in ((_184_180), (var_decl_q)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_184_181))
in (_184_182)::[])
in (FStar_List.append _184_183 c))
in if isEqName then begin
(FStar_Extraction_JavaScript_Ast.JSS_Block (c))::[]
end else begin
c
end))
end else begin
(translate_expr body ((name), (None)) (Some (c)) false lDecl (isMutable tys))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_84_321) -> begin
(failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args = (FStar_List.map (fun _84_332 -> (match (_84_332) with
| ((n, _84_329), t) -> begin
(let _184_187 = (let _184_186 = (let _184_185 = (translate_type t)
in Some (_184_185))
in ((n), (_184_186)))
in FStar_Extraction_JavaScript_Ast.JGP_Identifier (_184_187))
end)) args)
in (

let generic_t = (match ((FStar_ST.read lp_generic)) with
| [] -> begin
None
end
| _84_336 -> begin
(let _184_188 = (FStar_ST.read lp_generic)
in Some (_184_188))
end)
in (

let body_t = if (is_pure_expr body var) then begin
(let _184_189 = (translate_expr_pure body)
in FStar_Extraction_JavaScript_Ast.JS_BodyExpression (_184_189))
end else begin
(let _184_191 = (let _184_190 = (translate_expr body (("_res"), (None)) (Some ((FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))::[])) true lDecl true)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _184_190))
in FStar_Extraction_JavaScript_Ast.JS_BodyBlock (_184_191))
end
in (

let ret_t = (match ((Prims.snd var)) with
| None -> begin
None
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (_84_343, t2, _84_346) -> begin
Some (t2)
end
| _84_350 -> begin
None
end)
end)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (((None), (args), (body_t), (ret_t), (generic_t)))
in (

let lstmt = (match (lstmt) with
| Some (v) -> begin
v
end
| None -> begin
[]
end)
in (

let expr = if isDecl then begin
(FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((((Prims.fst var)), (None)))), (expr)))))::[]
end else begin
(

let _84_357 = (let _184_193 = (let _184_192 = (FStar_ST.read lDecl)
in (FStar_List.append (((Prims.fst var))::[]) _184_192))
in (FStar_ST.op_Colon_Equals lDecl _184_193))
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((((Prims.fst var)), (None)))), (Some (expr)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::[])
end
in (FStar_List.append expr lstmt))))))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let s1 = (let _184_194 = (translate_expr s1 var None true lDecl isMutableV)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_184_194))
in (

let s2 = (match (s2) with
| Some (v) -> begin
(let _184_196 = (let _184_195 = (translate_expr v var None true lDecl isMutableV)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_184_195))
in Some (_184_196))
end
| None -> begin
None
end)
in (

let c = if (is_pure_expr cond var) then begin
(let _184_199 = (let _184_198 = (let _184_197 = (translate_expr_pure cond)
in ((_184_197), (s1), (s2)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_184_198))
in (_184_199)::[])
end else begin
(let _184_200 = (translate_expr cond (("_cond"), (None)) (Some ((FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (s1), (s2))))::[])) true lDecl true)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _184_200))
end
in (

let c = if isDecl then begin
c
end else begin
(

let _84_371 = (let _184_202 = (let _184_201 = (FStar_ST.read lDecl)
in (FStar_List.append (((Prims.fst var))::[]) _184_201))
in (FStar_ST.op_Colon_Equals lDecl _184_202))
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) c))
end
in (match (lstmt) with
| Some (v) -> begin
(FStar_List.append c v)
end
| None -> begin
c
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_84_378) -> begin
(failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_84_381) -> begin
(failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(

let var = (let _184_204 = (let _184_203 = (translate_type in_e.FStar_Extraction_ML_Syntax.mlty)
in Some (_184_203))
in (((Prims.fst var)), (_184_204)))
in (translate_expr in_e var lstmt isDecl lDecl isMutableV))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let match_e = (let _184_205 = (FStar_Absyn_Util.gensym ())
in ((_184_205), (None)))
in (

let c = if (is_pure_expr e_in var) then begin
(let _184_212 = (let _184_209 = (let _184_208 = (let _184_207 = (let _184_206 = (translate_expr_pure e_in)
in Some (_184_206))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (match_e)), (_184_207)))
in ((_184_208), (FStar_Extraction_JavaScript_Ast.JSV_Const)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_184_209))
in (let _184_211 = (let _184_210 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (match_e)) var isMutableV lDecl)
in (_184_210)::[])
in (_184_212)::_184_211))
end else begin
(let _184_216 = (let _184_215 = (let _184_214 = (let _184_213 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (match_e)) var isMutableV lDecl)
in (_184_213)::[])
in Some (_184_214))
in (translate_expr e_in match_e _184_215 true lDecl true))
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (match_e)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _184_216))
end
in (

let c = if isDecl then begin
c
end else begin
(FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) c)
end
in (match (lstmt) with
| Some (v) -> begin
(FStar_List.append c v)
end
| None -> begin
c
end))))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(

let rec translate_seq = (fun l -> (match (l) with
| [] -> begin
(failwith "Empty list in [MLE_Seq]")
end
| (x)::[] -> begin
(translate_expr x var None isDecl lDecl isMutableV)
end
| (hd)::tl -> begin
(let _184_220 = (let _184_219 = (translate_seq tl)
in Some (_184_219))
in (translate_expr hd (("_"), (None)) _184_220 false lDecl true))
end))
in (

let c = (translate_seq ls)
in (match (lstmt) with
| Some (v) -> begin
(FStar_List.append c v)
end
| None -> begin
c
end)))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let args = (create_pure_args new_fv args var)
in (

let expr = (translate_arg_app e args var)
in (get_res expr (Some (new_fv))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let lexpr = (create_pure_args new_fv lexpr var)
in (

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
| _84_439 -> begin
(let _184_229 = (let _184_228 = (FStar_List.mapi (fun i x -> (let _184_227 = (let _184_226 = (let _184_225 = (let _184_224 = (let _184_223 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _184_223))
in ((_184_224), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_184_225))
in ((_184_226), (x), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_184_227))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _184_228))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_184_229))
end)
in (get_res expr (Some (new_fv))))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.map (fun _84_450 -> (match (_84_450) with
| (id, x) -> begin
(let _184_233 = (let _184_232 = (let _184_231 = (create_pure_args new_fv ((x)::[]) var)
in (FStar_List.nth _184_231 (Prims.parse_int "0")))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_184_232), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_184_233))
end)) fields)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))
in (get_res expr (Some (new_fv))))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.map (fun x -> (let _184_235 = (create_pure_args new_fv ((x)::[]) var)
in (FStar_List.nth _184_235 (Prims.parse_int "0")))) lexp)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSE_Array (Some (create_fields))
in (get_res expr (Some (new_fv))))))
end
| _84_460 -> begin
(failwith "todo: translation ml-expr")
end)))
and create_pure_args : FStar_Extraction_JavaScript_Ast.statement_t Prims.list FStar_ST.ref  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list = (fun new_fv args var -> (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _84_469) when ((c = "Nil") || (c = "None")) -> begin
(let _184_242 = (let _184_241 = (translate_expr_pure x)
in (let _184_240 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_184_241), (_184_240))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_184_242))
end
| _84_473 -> begin
if (is_pure_expr x var) then begin
(translate_expr_pure x)
end else begin
(

let fv_x = (FStar_Absyn_Util.gensym ())
in (

let c = (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (_84_476) -> begin
(

let _84_478 = (FStar_ST.op_Colon_Equals isEqVar true)
in (let _184_247 = (let _184_246 = (let _184_245 = (let _184_244 = (let _184_243 = (translate_expr_pure x)
in Some (_184_243))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (_184_244)))
in ((_184_245), (FStar_Extraction_JavaScript_Ast.JSV_Const)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_184_246))
in (_184_247)::[]))
end
| _84_481 -> begin
(let _184_248 = (FStar_ST.alloc [])
in (translate_expr x ((fv_x), (None)) None false _184_248 false))
end)
in (

let _84_483 = (let _184_250 = (let _184_249 = (FStar_ST.read new_fv)
in (FStar_List.append _184_249 c))
in (FStar_ST.op_Colon_Equals new_fv _184_250))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None))))))
end
end)) args))
and translate_arg_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e args var -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _184_257 = (let _184_256 = (FStar_Util.must (mk_op_bin op))
in (let _184_255 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _184_254 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_184_256), (_184_255), (_184_254)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_184_257))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _184_261 = (let _184_260 = (FStar_Util.must (mk_op_bool op))
in (let _184_259 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _184_258 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_184_260), (_184_259), (_184_258)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_184_261))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _184_264 = (let _184_263 = (FStar_Util.must (mk_op_un op))
in (let _184_262 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_184_263), (_184_262))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_184_264))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index")) -> begin
(let _184_268 = (let _184_267 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _184_266 = (let _184_265 = (FStar_List.nth args (Prims.parse_int "1"))
in FStar_Extraction_JavaScript_Ast.JSPM_Expression (_184_265))
in ((_184_267), (_184_266))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_184_268))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd")) -> begin
(let _184_276 = (let _184_275 = (let _184_273 = (let _184_272 = (let _184_271 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _184_270 = (let _184_269 = (FStar_List.nth args (Prims.parse_int "1"))
in FStar_Extraction_JavaScript_Ast.JSPM_Expression (_184_269))
in ((_184_271), (_184_270))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_184_272))
in FStar_Extraction_JavaScript_Ast.JGP_Expression (_184_273))
in (let _184_274 = (FStar_List.nth args (Prims.parse_int "2"))
in ((_184_275), (_184_274))))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_184_276))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.read")) -> begin
(let _184_278 = (let _184_277 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_184_277), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0")))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_184_278))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.write")) -> begin
(

let expr = (let _184_280 = (let _184_279 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_184_279), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0")))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_184_280))
in (let _184_282 = (let _184_281 = (FStar_List.nth args (Prims.parse_int "1"))
in ((FStar_Extraction_JavaScript_Ast.JGP_Expression (expr)), (_184_281)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_184_282)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.alloc") -> begin
(let _184_285 = (let _184_284 = (let _184_283 = (FStar_List.nth args (Prims.parse_int "0"))
in (_184_283)::[])
in Some (_184_284))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_184_285))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(let _184_288 = (let _184_287 = (let _184_286 = (getName ((path), (function_name)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_184_286))
in ((_184_287), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_184_288))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _84_520) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))
end
| _84_524 -> begin
if (is_pure_expr e var) then begin
(let _184_290 = (let _184_289 = (translate_expr_pure e)
in ((_184_289), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_184_290))
end else begin
(failwith "todo: translation [MLE_App]")
end
end))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _84_530) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
(let _184_292 = (getName ((path), (n)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_184_292))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(let _184_294 = (let _184_293 = (FStar_List.map translate_expr_pure lexp)
in Some (_184_293))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_184_294))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _84_545 -> (match (_84_545) with
| (id, x) -> begin
(let _184_297 = (let _184_296 = (translate_expr_pure x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_184_296), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_184_297))
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
(let _184_305 = (let _184_304 = (let _184_302 = (let _184_301 = (let _184_300 = (let _184_299 = (let _184_298 = (translate_expr_pure hd)
in (_184_298)::[])
in Some (_184_299))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_184_300))
in ((_184_301), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("concat"), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_184_302))
in (let _184_303 = (FStar_List.map translate_expr_pure tl)
in ((_184_304), (_184_303))))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_184_305))
end)
end
| x when ((x = "Some") || (x = "None")) -> begin
(match (lexpr) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| (hd)::tl -> begin
(let _184_306 = (FStar_List.map translate_expr_pure lexpr)
in (FStar_List.nth _184_306 (Prims.parse_int "0")))
end)
end
| _84_564 -> begin
(let _184_316 = (let _184_315 = (FStar_List.mapi (fun i x -> (let _184_314 = (let _184_313 = (let _184_311 = (let _184_310 = (let _184_309 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _184_309))
in ((_184_310), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_184_311))
in (let _184_312 = (translate_expr_pure x)
in ((_184_313), (_184_312), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_184_314))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _184_315))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_184_316))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _84_569, _84_571) -> begin
(translate_expr_pure e)
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args = (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _84_583) when ((c = "Nil") || (c = "None")) -> begin
(let _184_320 = (let _184_319 = (translate_expr_pure x)
in (let _184_318 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_184_319), (_184_318))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_184_320))
end
| _84_587 -> begin
(translate_expr_pure x)
end)) args)
in (translate_arg_app e args ((""), (None))))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, (path, name)) -> begin
(let _184_322 = (let _184_321 = (translate_expr_pure expr)
in ((_184_321), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" name)), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_184_322))
end
| _84_596 -> begin
(failwith "todo: translation ml-expr-pure")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  Prims.bool  ->  Prims.string Prims.list FStar_ST.ref  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x var isMutableV lDecl -> (match (lb) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end
| ((p, guard, expr_r))::tl -> begin
(

let expr_t = if (is_pure_expr expr_r var) then begin
(let _184_331 = (let _184_329 = (let _184_328 = (translate_expr_pure expr_r)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_184_328)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_184_329))
in (FStar_All.pipe_right _184_331 (fun _184_330 -> FStar_Extraction_JavaScript_Ast.JSS_Expression (_184_330))))
end else begin
(let _184_333 = (translate_expr expr_r var None true lDecl isMutableV)
in (FStar_All.pipe_right _184_333 (fun _184_332 -> FStar_Extraction_JavaScript_Ast.JSS_Seq (_184_332))))
end
in (let _184_334 = (translate_match tl fv_x var isMutableV lDecl)
in (translate_pat_guard ((p), (guard)) fv_x expr_t _184_334)))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _84_612 fv_x s1 s2 -> (match (_84_612) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _184_340 = (let _184_339 = (translate_expr_pure v_guard)
in ((_184_339), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_184_340))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _84_626) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Seq ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _184_348 = (let _184_347 = (let _184_346 = (let _184_345 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_184_345)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_184_346))
in ((_184_347), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_184_348))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((path, c), lp) -> begin
(

let rec translate_p_ctor = (fun lp fv_x s1 s2 i -> (

let new_fv_x = (match (c) with
| x when (x = "Some") -> begin
fv_x
end
| x when ((x = "Cons") && (i = (Prims.parse_int "0"))) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0")))))))
end
| x when ((x = "Cons") && (i = (Prims.parse_int "1"))) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("slice(1)"), (None))))))
end
| _84_648 -> begin
(let _184_363 = (let _184_362 = (let _184_361 = (let _184_360 = (let _184_359 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _184_359))
in ((_184_360), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_184_361))
in ((fv_x), (_184_362)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_184_363))
end)
in (match (lp) with
| [] -> begin
s1
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _184_364 = (translate_p_ctor tl fv_x s1 s2 (i + (Prims.parse_int "1")))
in (translate_pat hd new_fv_x _184_364 s2))
end)))
in (

let if_stmt = (fun if_cond -> (let _184_368 = (let _184_367 = (translate_p_ctor lp fv_x s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_184_367), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_184_368)))
in (match (c) with
| x when (x = "Cons") -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_GreaterThan), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("length"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0"))))))))
end
| x when (x = "Nil") -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_Equal), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("length"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0"))))))))
end
| x when (x = "Some") -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_NotEqual), (fv_x), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))))))
end
| x when (x = "None") -> begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))))))
end
| _84_663 -> begin
(

let isSimple = (match (fv_x) with
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (_84_665) -> begin
true
end
| _84_668 -> begin
false
end)
in if isSimple then begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))))
end else begin
(

let new_name = (FStar_Absyn_Util.gensym ())
in (

let if_cond = FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))
in (let _184_373 = (let _184_372 = (let _184_371 = (let _184_370 = (let _184_369 = (translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))) s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_184_369), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_184_370))
in (_184_371)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((new_name), (None)))), (Some (fv_x)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::_184_372)
in FStar_Extraction_JavaScript_Ast.JSS_Seq (_184_373))))
end)
end)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (lp) -> begin
(

let rec translate_p_branch = (fun lp fv_x s1 s2 -> (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_branch")
end
| (x)::[] -> begin
(translate_pat x fv_x s1 s2)
end
| (hd)::tl -> begin
(let _184_382 = (translate_p_branch tl fv_x s1 s2)
in (translate_pat hd fv_x s1 _184_382))
end))
in (translate_p_branch lp fv_x s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, lp) -> begin
(

let rec translate_p_record = (fun lp fv_x s1 s2 -> (

let new_fv_x = (fun n -> FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" n)), (None)))))))
in (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_record")
end
| (x)::[] -> begin
(translate_pat (Prims.snd x) (new_fv_x (Prims.fst x)) s1 s2)
end
| (hd)::tl -> begin
(let _184_393 = (translate_p_record tl fv_x s1 s2)
in (translate_pat (Prims.snd hd) (new_fv_x (Prims.fst hd)) _184_393 s2))
end)))
in (translate_p_record lp fv_x s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(

let rec translate_p_tuple = (fun lp d fv_x s1 s2 -> (

let new_fv_x = (let _184_408 = (let _184_407 = (let _184_406 = (let _184_405 = (let _184_404 = (FStar_Util.string_of_int d)
in ((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int d))), (_184_404)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_184_405))
in FStar_Extraction_JavaScript_Ast.JSPM_Expression (_184_406))
in ((fv_x), (_184_407)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_184_408))
in (match (lp) with
| [] -> begin
(failwith "Empty list in translate_p_tuple")
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _184_409 = (translate_p_tuple tl (d + (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat hd new_fv_x _184_409 s2))
end)))
in (translate_p_tuple lp (Prims.parse_int "0") fv_x s1 s2))
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, _84_723) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_84_729) -> begin
(failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_84_734) -> begin
(failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _84_742) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((id), (None)))), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _184_412 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_184_412))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _84_749, t2) -> begin
(let _184_417 = (let _184_416 = (let _184_414 = (let _184_413 = (translate_type t1)
in (((("_1"), (None))), (_184_413)))
in (_184_414)::[])
in (let _184_415 = (translate_type t2)
in ((_184_416), (_184_415), (None))))
in FStar_Extraction_JavaScript_Ast.JST_Function (_184_417))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.ref") -> begin
(let _184_419 = (let _184_418 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_type _184_418))
in FStar_Extraction_JavaScript_Ast.JST_Array (_184_419))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _184_422 = (let _184_421 = (let _184_420 = (getName p)
in FStar_Extraction_JavaScript_Ast.Unqualified (_184_420))
in ((_184_421), (None)))
in FStar_Extraction_JavaScript_Ast.JST_Generic (_184_422))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _184_423 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _184_423)) then begin
(let _184_424 = (FStar_List.map translate_type args)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_184_424))
end else begin
(

let args_t = (match (args) with
| [] -> begin
None
end
| _84_769 -> begin
(let _184_426 = (FStar_List.map translate_type args)
in (FStar_All.pipe_right _184_426 (fun _184_425 -> Some (_184_425))))
end)
in (let _184_429 = (let _184_428 = (let _184_427 = (getName ((path), (name)))
in FStar_Extraction_JavaScript_Ast.Unqualified (_184_427))
in ((_184_428), (args_t)))
in FStar_Extraction_JavaScript_Ast.JST_Generic (_184_429)))
end
end
end))




