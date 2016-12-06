
open Prims

type file =
(Prims.string * FStar_Extraction_JavaScript_Ast.t)


type env =
{names : name Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; module_name = module_name})


let mk_op_bin : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_bin Prims.option = (fun _82_1 -> (match (_82_1) with
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
| _82_25 -> begin
None
end))


let is_op_bin : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bin op) <> None))


let mk_op_un : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_un Prims.option = (fun _82_2 -> (match (_82_2) with
| "op_Negation" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSU_Not)
end
| "op_Minus" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSU_Minus)
end
| _82_31 -> begin
None
end))


let is_op_un : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_un op) <> None))


let mk_op_bool : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_log Prims.option = (fun _82_3 -> (match (_82_3) with
| "op_AmpAmp" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_And)
end
| "op_BarBar" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_Or)
end
| _82_37 -> begin
None
end))


let is_op_bool : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bool op) <> None))


let mk_standart_type : Prims.string  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option = (fun _82_4 -> (match (_82_4) with
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
| _82_46 -> begin
None
end))


let is_standart_type : Prims.string  ->  Prims.bool = (fun t -> ((mk_standart_type t) <> None))


let float_of_int : Prims.int  ->  FStar_BaseTypes.float = (fun i -> (FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)))


let export_modules : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let current_module_name : Prims.string FStar_ST.ref = (FStar_ST.alloc "")


let lp_generic : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let isEqVar : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let getName = (fun _82_51 -> (match (_82_51) with
| (path, n) -> begin
(

let path = (FStar_String.concat "_" path)
in if ((path = (FStar_ST.read current_module_name)) || (path = "")) then begin
((n), (None))
end else begin
(

let _82_54 = if (not ((let _179_37 = (FStar_ST.read export_modules)
in (FStar_List.existsb (fun x -> (x = path)) _179_37)))) then begin
(let _179_39 = (let _179_38 = (FStar_ST.read export_modules)
in (FStar_List.append ((path)::[]) _179_38))
in (FStar_ST.op_Colon_Equals export_modules _179_39))
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
| FStar_Extraction_ML_Syntax.MLE_Var (n, _82_66) -> begin
(n <> (Prims.fst var))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, _82_71) -> begin
(is_pure_expr expr var)
end
| FStar_Extraction_ML_Syntax.MLE_CTor (p, le) -> begin
(not ((let _179_43 = (FStar_List.map (fun x -> (is_pure_expr x var)) le)
in (FStar_List.contains false _179_43))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (le) -> begin
(not ((let _179_45 = (FStar_List.map (fun x -> (is_pure_expr x var)) le)
in (FStar_List.contains false _179_45))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_83, lne) -> begin
(not ((let _179_47 = (FStar_List.map (fun _82_89 -> (match (_82_89) with
| (n, e) -> begin
(is_pure_expr e var)
end)) lne)
in (FStar_List.contains false _179_47))))
end
| FStar_Extraction_ML_Syntax.MLE_App (_82_91, args) -> begin
(not ((let _179_49 = (FStar_List.map (fun x -> (is_pure_expr x var)) args)
in (FStar_List.contains false _179_49))))
end
| _82_97 -> begin
false
end))


let isMutable = (fun tys -> (match (tys) with
| None -> begin
false
end
| Some (_82_101, ty) -> begin
(match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_82_106, p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.ref") -> begin
true
end
| _82_111 -> begin
false
end)
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_113 -> (match (_82_113) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_122 = m
in (match (_82_122) with
| ((prefix, final), _82_119, _82_121) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_132 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (

let _82_134 = (FStar_ST.op_Colon_Equals export_modules [])
in (let _179_85 = (translate_module m)
in Some (_179_85))))
end)
with
| e -> begin
(

let _82_128 = (let _179_87 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_87))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_140 -> (match (_82_140) with
| (module_name, modul, _82_139) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let _82_146 = (FStar_ST.op_Colon_Equals current_module_name (FStar_String.concat "_" module_name))
in (

let res = (FStar_List.filter_map translate_decl decls)
in (

let create_module_imports = (let _179_94 = (let _179_92 = (let _179_90 = (FStar_ST.read export_modules)
in (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (((m), (None)))) _179_90))
in (FStar_All.pipe_right _179_92 (fun _179_91 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_91))))
in (FStar_All.pipe_right _179_94 (fun _179_93 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_93))))
in (FStar_List.append ((create_module_imports)::[]) res))))
end
| _82_152 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (_82_156, c_flag, lfunc) -> begin
(

let for1 = (fun _82_170 -> (match (_82_170) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, _82_168); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = (

let _82_171 = (FStar_ST.op_Colon_Equals lp_generic [])
in if ((not (pt)) || unit_b) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some (lp, ty) -> begin
(

let _82_182 = (let _179_99 = (FStar_List.map (fun _82_181 -> (match (_82_181) with
| (id, _82_180) -> begin
id
end)) lp)
in (FStar_ST.op_Colon_Equals lp_generic _179_99))
in (let _179_101 = (translate_type ty)
in (FStar_All.pipe_right _179_101 (fun _179_100 -> Some (_179_100)))))
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
in (let _179_106 = (let _179_105 = (let _179_104 = (let _179_103 = (let _179_102 = (translate_expr_pure expr)
in Some (_179_102))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (_179_103)))
in ((_179_104), (var_decl_q)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_105))
in (_179_106)::[]))
end else begin
(let _179_107 = (FStar_ST.alloc [])
in (translate_expr expr ((name), (t)) None false _179_107 (isMutable tys)))
end
in if is_private then begin
c
end else begin
(FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (FStar_Extraction_JavaScript_Ast.JSS_Block (c))), (FStar_Extraction_JavaScript_Ast.ExportValue))))::[]
end)))
end))
in (let _179_113 = (let _179_111 = (let _179_109 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _179_109 (fun _179_108 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_108))))
in (FStar_All.pipe_right _179_111 (fun _179_110 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_110))))
in (FStar_All.pipe_right _179_113 (fun _179_112 -> Some (_179_112)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_189) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_192, name, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| _82_201 -> begin
(let _179_116 = (FStar_List.map (fun _82_205 -> (match (_82_205) with
| (id, _82_204) -> begin
id
end)) tparams)
in (FStar_All.pipe_right _179_116 (fun _179_115 -> Some (_179_115))))
end)
in (

let forbody = (fun body -> (

let get_export = (fun stmt -> (FStar_All.pipe_right ((FStar_Extraction_JavaScript_Ast.JSE_Declaration (stmt)), (FStar_Extraction_JavaScript_Ast.ExportType)) (fun _179_121 -> FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (_179_121))))
in (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _179_124 = (let _179_123 = (let _179_122 = (translate_type t)
in ((((name), (None))), (tparams), (_179_122)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_123))
in (get_export _179_124))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _82_218 -> (match (_82_218) with
| (n, t) -> begin
(let _179_126 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_179_126)))
end)) fields)
in (get_export (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.mapi (fun i t -> (let _179_137 = (let _179_135 = (let _179_134 = (let _179_133 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_133))
in ((_179_134), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_135))
in (let _179_136 = (translate_type t)
in ((_179_137), (_179_136))))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_230 -> (match (_82_230) with
| (n, l) -> begin
(let _179_144 = (let _179_143 = (let _179_142 = (let _179_141 = (let _179_140 = (let _179_139 = (fields_t l)
in (FStar_List.append (tag n) _179_139))
in ((_179_140), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_141))
in ((((n), (None))), (tparams), (_179_142)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_143))
in (get_export _179_144))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _179_147 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((x), (None)))), (None)))) t)
in (FStar_All.pipe_right _179_147 (fun _179_146 -> Some (_179_146))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun _82_239 -> (match (_82_239) with
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
(FStar_All.failwith "todo: translate_decl [MLM_Ty] with empty body")
end
| Some (v) -> begin
(forbody v)
end)
in (let _179_151 = (FStar_All.pipe_right body_t (fun _179_149 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_149)))
in (FStar_All.pipe_right _179_151 (fun _179_150 -> Some (_179_150)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_247) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_250) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _179_154 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block ([])) (fun _179_152 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_152)))
in (FStar_All.pipe_right _179_154 (fun _179_153 -> Some (_179_153))))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_257) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
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
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (_82_274) -> begin
(

let _82_276 = (FStar_ST.op_Colon_Equals isAssgmnt ((FStar_Extraction_JavaScript_Ast.JSS_Expression (expr))::[]))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), (""))))
end
| _82_279 -> begin
expr
end)
in (

let expr = if isDecl then begin
FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (expr))))
end else begin
(

let _82_281 = (let _179_166 = (let _179_165 = (FStar_ST.read lDecl)
in (FStar_List.append (((Prims.fst var))::[]) _179_165))
in (FStar_ST.op_Colon_Equals lDecl _179_166))
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

let _82_287 = (FStar_ST.op_Colon_Equals isEqVar false)
in (let _179_169 = (FStar_ST.read v)
in (let _179_168 = (let _179_167 = (FStar_ST.read isAssgmnt)
in (FStar_List.append _179_167 ((FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append ((expr)::[]) lstmt)))::[])))
in (FStar_List.append _179_169 _179_168))))
end else begin
(let _179_172 = (FStar_ST.read v)
in (let _179_171 = (let _179_170 = (FStar_ST.read isAssgmnt)
in (FStar_List.append _179_170 (FStar_List.append ((expr)::[]) lstmt)))
in (FStar_List.append _179_172 _179_171)))
end
end
| None -> begin
(let _179_173 = (FStar_ST.read isAssgmnt)
in (FStar_List.append _179_173 (FStar_List.append ((expr)::[]) lstmt)))
end))))))
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e var) -> begin
(

let expr = (translate_expr_pure e)
in (get_res expr None))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((_82_293, _82_295, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_302); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let isEqName = (let _179_175 = (FStar_ST.read lDecl)
in (FStar_List.existsb (fun x -> (x = name)) _179_175))
in (

let lDecl = if isEqName then begin
lDecl
end else begin
(

let _82_312 = (let _179_177 = (let _179_176 = (FStar_ST.read lDecl)
in (FStar_List.append ((name)::[]) _179_176))
in (FStar_ST.op_Colon_Equals lDecl _179_177))
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

let c = (let _179_183 = (let _179_182 = (let _179_181 = (let _179_180 = (let _179_179 = (let _179_178 = (translate_expr_pure body)
in Some (_179_178))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (_179_179)))
in ((_179_180), (var_decl_q)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_181))
in (_179_182)::[])
in (FStar_List.append _179_183 c))
in if isEqName then begin
(FStar_Extraction_JavaScript_Ast.JSS_Block (c))::[]
end else begin
c
end))
end else begin
(translate_expr body ((name), (None)) (Some (c)) false lDecl (isMutable tys))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_319) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args = (FStar_List.map (fun _82_330 -> (match (_82_330) with
| ((n, _82_327), t) -> begin
(let _179_187 = (let _179_186 = (let _179_185 = (translate_type t)
in Some (_179_185))
in ((n), (_179_186)))
in FStar_Extraction_JavaScript_Ast.JGP_Identifier (_179_187))
end)) args)
in (

let generic_t = (match ((FStar_ST.read lp_generic)) with
| [] -> begin
None
end
| _82_334 -> begin
(let _179_188 = (FStar_ST.read lp_generic)
in Some (_179_188))
end)
in (

let body_t = if (is_pure_expr body var) then begin
(let _179_189 = (translate_expr_pure body)
in FStar_Extraction_JavaScript_Ast.JS_BodyExpression (_179_189))
end else begin
(let _179_191 = (let _179_190 = (translate_expr body (("_res"), (None)) (Some ((FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))::[])) true lDecl true)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _179_190))
in FStar_Extraction_JavaScript_Ast.JS_BodyBlock (_179_191))
end
in (

let ret_t = (match ((Prims.snd var)) with
| None -> begin
None
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (_82_341, t2, _82_344) -> begin
Some (t2)
end
| _82_348 -> begin
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

let _82_355 = (let _179_193 = (let _179_192 = (FStar_ST.read lDecl)
in (FStar_List.append (((Prims.fst var))::[]) _179_192))
in (FStar_ST.op_Colon_Equals lDecl _179_193))
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((((Prims.fst var)), (None)))), (Some (expr)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::[])
end
in (FStar_List.append expr lstmt))))))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let s1 = (let _179_194 = (translate_expr s1 var None true lDecl isMutableV)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_194))
in (

let s2 = (match (s2) with
| Some (v) -> begin
(let _179_196 = (let _179_195 = (translate_expr v var None true lDecl isMutableV)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_195))
in Some (_179_196))
end
| None -> begin
None
end)
in (

let c = if (is_pure_expr cond var) then begin
(let _179_199 = (let _179_198 = (let _179_197 = (translate_expr_pure cond)
in ((_179_197), (s1), (s2)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_198))
in (_179_199)::[])
end else begin
(let _179_200 = (translate_expr cond (("_cond"), (None)) (Some ((FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (s1), (s2))))::[])) true lDecl true)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _179_200))
end
in (

let c = if isDecl then begin
c
end else begin
(

let _82_369 = (let _179_202 = (let _179_201 = (FStar_ST.read lDecl)
in (FStar_List.append (((Prims.fst var))::[]) _179_201))
in (FStar_ST.op_Colon_Equals lDecl _179_202))
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
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_376) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_379) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(

let var = (let _179_204 = (let _179_203 = (translate_type in_e.FStar_Extraction_ML_Syntax.mlty)
in Some (_179_203))
in (((Prims.fst var)), (_179_204)))
in (translate_expr in_e var lstmt isDecl lDecl isMutableV))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let match_e = (let _179_205 = (FStar_Absyn_Util.gensym ())
in ((_179_205), (None)))
in (

let c = if (is_pure_expr e_in var) then begin
(let _179_212 = (let _179_209 = (let _179_208 = (let _179_207 = (let _179_206 = (translate_expr_pure e_in)
in Some (_179_206))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (match_e)), (_179_207)))
in ((_179_208), (FStar_Extraction_JavaScript_Ast.JSV_Const)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_209))
in (let _179_211 = (let _179_210 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (match_e)) var isMutableV lDecl)
in (_179_210)::[])
in (_179_212)::_179_211))
end else begin
(let _179_216 = (let _179_215 = (let _179_214 = (let _179_213 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (match_e)) var isMutableV lDecl)
in (_179_213)::[])
in Some (_179_214))
in (translate_expr e_in match_e _179_215 true lDecl true))
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (match_e)), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _179_216))
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
(FStar_All.failwith "Empty list in [MLE_Seq]")
end
| (x)::[] -> begin
(translate_expr x var None isDecl lDecl isMutableV)
end
| (hd)::tl -> begin
(let _179_220 = (let _179_219 = (translate_seq tl)
in Some (_179_219))
in (translate_expr hd (("_"), (None)) _179_220 false lDecl true))
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
| _82_437 -> begin
(let _179_229 = (let _179_228 = (FStar_List.mapi (fun i x -> (let _179_227 = (let _179_226 = (let _179_225 = (let _179_224 = (let _179_223 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_223))
in ((_179_224), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_225))
in ((_179_226), (x), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_227))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _179_228))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_229))
end)
in (get_res expr (Some (new_fv))))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.map (fun _82_448 -> (match (_82_448) with
| (id, x) -> begin
(let _179_233 = (let _179_232 = (let _179_231 = (create_pure_args new_fv ((x)::[]) var)
in (FStar_List.nth _179_231 (Prims.parse_int "0")))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_232), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_233))
end)) fields)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))
in (get_res expr (Some (new_fv))))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.map (fun x -> (let _179_235 = (create_pure_args new_fv ((x)::[]) var)
in (FStar_List.nth _179_235 (Prims.parse_int "0")))) lexp)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSE_Array (Some (create_fields))
in (get_res expr (Some (new_fv))))))
end
| _82_458 -> begin
(FStar_All.failwith "todo: translation ml-expr")
end)))
and create_pure_args : FStar_Extraction_JavaScript_Ast.statement_t Prims.list FStar_ST.ref  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list = (fun new_fv args var -> (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _82_467) when ((c = "Nil") || (c = "None")) -> begin
(let _179_242 = (let _179_241 = (translate_expr_pure x)
in (let _179_240 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_241), (_179_240))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_242))
end
| _82_471 -> begin
if (is_pure_expr x var) then begin
(translate_expr_pure x)
end else begin
(

let fv_x = (FStar_Absyn_Util.gensym ())
in (

let c = (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (_82_474) -> begin
(

let _82_476 = (FStar_ST.op_Colon_Equals isEqVar true)
in (let _179_247 = (let _179_246 = (let _179_245 = (let _179_244 = (let _179_243 = (translate_expr_pure x)
in Some (_179_243))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (_179_244)))
in ((_179_245), (FStar_Extraction_JavaScript_Ast.JSV_Const)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_246))
in (_179_247)::[]))
end
| _82_479 -> begin
(let _179_248 = (FStar_ST.alloc [])
in (translate_expr x ((fv_x), (None)) None false _179_248 false))
end)
in (

let _82_481 = (let _179_250 = (let _179_249 = (FStar_ST.read new_fv)
in (FStar_List.append _179_249 c))
in (FStar_ST.op_Colon_Equals new_fv _179_250))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None))))))
end
end)) args))
and translate_arg_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e args var -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_257 = (let _179_256 = (FStar_Util.must (mk_op_bin op))
in (let _179_255 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_254 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_256), (_179_255), (_179_254)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_257))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_261 = (let _179_260 = (FStar_Util.must (mk_op_bool op))
in (let _179_259 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_258 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_260), (_179_259), (_179_258)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_261))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_264 = (let _179_263 = (FStar_Util.must (mk_op_un op))
in (let _179_262 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_179_263), (_179_262))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_264))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index")) -> begin
(let _179_268 = (let _179_267 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_266 = (let _179_265 = (FStar_List.nth args (Prims.parse_int "1"))
in FStar_Extraction_JavaScript_Ast.JSPM_Expression (_179_265))
in ((_179_267), (_179_266))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_268))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd")) -> begin
(let _179_276 = (let _179_275 = (let _179_273 = (let _179_272 = (let _179_271 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_270 = (let _179_269 = (FStar_List.nth args (Prims.parse_int "1"))
in FStar_Extraction_JavaScript_Ast.JSPM_Expression (_179_269))
in ((_179_271), (_179_270))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_272))
in FStar_Extraction_JavaScript_Ast.JGP_Expression (_179_273))
in (let _179_274 = (FStar_List.nth args (Prims.parse_int "2"))
in ((_179_275), (_179_274))))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_276))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.read")) -> begin
(let _179_278 = (let _179_277 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_179_277), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0")))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_278))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.write")) -> begin
(

let expr = (let _179_280 = (let _179_279 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_179_279), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("0")))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_280))
in (let _179_282 = (let _179_281 = (FStar_List.nth args (Prims.parse_int "1"))
in ((FStar_Extraction_JavaScript_Ast.JGP_Expression (expr)), (_179_281)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_282)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.alloc") -> begin
(let _179_285 = (let _179_284 = (let _179_283 = (FStar_List.nth args (Prims.parse_int "0"))
in (_179_283)::[])
in Some (_179_284))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_285))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(let _179_288 = (let _179_287 = (let _179_286 = (getName ((path), (function_name)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_286))
in ((_179_287), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_288))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_518) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))
end
| _82_522 -> begin
if (is_pure_expr e var) then begin
(let _179_290 = (let _179_289 = (translate_expr_pure e)
in ((_179_289), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_290))
end else begin
(FStar_All.failwith "todo: translation [MLE_App]")
end
end))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_528) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
(let _179_292 = (getName ((path), (n)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_292))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(let _179_294 = (let _179_293 = (FStar_List.map translate_expr_pure lexp)
in Some (_179_293))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_294))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _82_543 -> (match (_82_543) with
| (id, x) -> begin
(let _179_297 = (let _179_296 = (translate_expr_pure x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_296), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_297))
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
(let _179_305 = (let _179_304 = (let _179_302 = (let _179_301 = (let _179_300 = (let _179_299 = (let _179_298 = (translate_expr_pure hd)
in (_179_298)::[])
in Some (_179_299))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_300))
in ((_179_301), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("concat"), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_302))
in (let _179_303 = (FStar_List.map translate_expr_pure tl)
in ((_179_304), (_179_303))))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_305))
end)
end
| x when ((x = "Some") || (x = "None")) -> begin
(match (lexpr) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| (hd)::tl -> begin
(let _179_306 = (FStar_List.map translate_expr_pure lexpr)
in (FStar_List.nth _179_306 (Prims.parse_int "0")))
end)
end
| _82_562 -> begin
(let _179_316 = (let _179_315 = (FStar_List.mapi (fun i x -> (let _179_314 = (let _179_313 = (let _179_311 = (let _179_310 = (let _179_309 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_309))
in ((_179_310), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_311))
in (let _179_312 = (translate_expr_pure x)
in ((_179_313), (_179_312), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_314))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _179_315))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_316))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _82_567, _82_569) -> begin
(translate_expr_pure e)
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args = (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _82_581) when ((c = "Nil") || (c = "None")) -> begin
(let _179_320 = (let _179_319 = (translate_expr_pure x)
in (let _179_318 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_319), (_179_318))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_320))
end
| _82_585 -> begin
(translate_expr_pure x)
end)) args)
in (translate_arg_app e args ((""), (None))))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, (path, name)) -> begin
(let _179_322 = (let _179_321 = (translate_expr_pure expr)
in ((_179_321), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" name)), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_322))
end
| _82_594 -> begin
(FStar_All.failwith "todo: translation ml-expr-pure")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  Prims.bool  ->  Prims.string Prims.list FStar_ST.ref  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x var isMutableV lDecl -> (match (lb) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end
| ((p, guard, expr_r))::tl -> begin
(

let expr_t = if (is_pure_expr expr_r var) then begin
(let _179_331 = (let _179_329 = (let _179_328 = (translate_expr_pure expr_r)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_328)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_329))
in (FStar_All.pipe_right _179_331 (fun _179_330 -> FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_330))))
end else begin
(let _179_333 = (translate_expr expr_r var None true lDecl isMutableV)
in (FStar_All.pipe_right _179_333 (fun _179_332 -> FStar_Extraction_JavaScript_Ast.JSS_Seq (_179_332))))
end
in (let _179_334 = (translate_match tl fv_x var isMutableV lDecl)
in (translate_pat_guard ((p), (guard)) fv_x expr_t _179_334)))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_610 fv_x s1 s2 -> (match (_82_610) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_340 = (let _179_339 = (translate_expr_pure v_guard)
in ((_179_339), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_340))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_624) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Seq ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_348 = (let _179_347 = (let _179_346 = (let _179_345 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_345)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_346))
in ((_179_347), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_348))
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
| _82_646 -> begin
(let _179_363 = (let _179_362 = (let _179_361 = (let _179_360 = (let _179_359 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_359))
in ((_179_360), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_361))
in ((fv_x), (_179_362)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_363))
end)
in (match (lp) with
| [] -> begin
s1
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_364 = (translate_p_ctor tl fv_x s1 s2 (i + (Prims.parse_int "1")))
in (translate_pat hd new_fv_x _179_364 s2))
end)))
in (

let if_stmt = (fun if_cond -> (let _179_368 = (let _179_367 = (translate_p_ctor lp fv_x s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_179_367), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_368)))
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
| _82_661 -> begin
(

let isSimple = (match (fv_x) with
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (_82_663) -> begin
true
end
| _82_666 -> begin
false
end)
in if isSimple then begin
(if_stmt (FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))))
end else begin
(

let new_name = (FStar_Absyn_Util.gensym ())
in (

let if_cond = FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))
in (let _179_373 = (let _179_372 = (let _179_371 = (let _179_370 = (let _179_369 = (translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))) s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_179_369), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_370))
in (_179_371)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((new_name), (None)))), (Some (fv_x)))), (FStar_Extraction_JavaScript_Ast.JSV_Const))))::_179_372)
in FStar_Extraction_JavaScript_Ast.JSS_Seq (_179_373))))
end)
end)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (lp) -> begin
(

let rec translate_p_branch = (fun lp fv_x s1 s2 -> (match (lp) with
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_branch")
end
| (x)::[] -> begin
(translate_pat x fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_382 = (translate_p_branch tl fv_x s1 s2)
in (translate_pat hd fv_x s1 _179_382))
end))
in (translate_p_branch lp fv_x s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, lp) -> begin
(

let rec translate_p_record = (fun lp fv_x s1 s2 -> (

let new_fv_x = (fun n -> FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" n)), (None)))))))
in (match (lp) with
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_record")
end
| (x)::[] -> begin
(translate_pat (Prims.snd x) (new_fv_x (Prims.fst x)) s1 s2)
end
| (hd)::tl -> begin
(let _179_393 = (translate_p_record tl fv_x s1 s2)
in (translate_pat (Prims.snd hd) (new_fv_x (Prims.fst hd)) _179_393 s2))
end)))
in (translate_p_record lp fv_x s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(

let rec translate_p_tuple = (fun lp d fv_x s1 s2 -> (

let new_fv_x = (let _179_408 = (let _179_407 = (let _179_406 = (let _179_405 = (let _179_404 = (FStar_Util.string_of_int d)
in ((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int d))), (_179_404)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_405))
in FStar_Extraction_JavaScript_Ast.JSPM_Expression (_179_406))
in ((fv_x), (_179_407)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_408))
in (match (lp) with
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_tuple")
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_409 = (translate_p_tuple tl (d + (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat hd new_fv_x _179_409 s2))
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
| FStar_Extraction_ML_Syntax.MLC_Int (s, _82_721) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_727) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_732) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _82_740) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((id), (None)))), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _179_412 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_412))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_747, t2) -> begin
(let _179_417 = (let _179_416 = (let _179_414 = (let _179_413 = (translate_type t1)
in (((("_1"), (None))), (_179_413)))
in (_179_414)::[])
in (let _179_415 = (translate_type t2)
in ((_179_416), (_179_415), (None))))
in FStar_Extraction_JavaScript_Ast.JST_Function (_179_417))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.ref") -> begin
(let _179_419 = (let _179_418 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_type _179_418))
in FStar_Extraction_JavaScript_Ast.JST_Array (_179_419))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _179_422 = (let _179_421 = (let _179_420 = (getName p)
in FStar_Extraction_JavaScript_Ast.Unqualified (_179_420))
in ((_179_421), (None)))
in FStar_Extraction_JavaScript_Ast.JST_Generic (_179_422))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _179_423 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _179_423)) then begin
(let _179_424 = (FStar_List.map translate_type args)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_424))
end else begin
(

let args_t = (match (args) with
| [] -> begin
None
end
| _82_767 -> begin
(let _179_426 = (FStar_List.map translate_type args)
in (FStar_All.pipe_right _179_426 (fun _179_425 -> Some (_179_425))))
end)
in (let _179_429 = (let _179_428 = (let _179_427 = (getName ((path), (name)))
in FStar_Extraction_JavaScript_Ast.Unqualified (_179_427))
in ((_179_428), (args_t)))
in FStar_Extraction_JavaScript_Ast.JST_Generic (_179_429)))
end
end
end))




