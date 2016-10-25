
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
| "op_Colon_Equals" -> begin
(FStar_All.failwith "todo: translation [:=]")
end
| _82_26 -> begin
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
| "op_Bang" -> begin
(FStar_All.failwith "todo: translation [!]")
end
| _82_33 -> begin
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
| _82_39 -> begin
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
| _82_48 -> begin
None
end))


let is_standart_type : Prims.string  ->  Prims.bool = (fun t -> ((mk_standart_type t) <> None))


let float_of_int : Prims.int  ->  FStar_BaseTypes.float = (fun i -> (FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)))


let export_modules : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let current_module_name : Prims.string FStar_ST.ref = (FStar_ST.alloc "")


let getName : (Prims.string Prims.list * Prims.string)  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun _82_53 -> (match (_82_53) with
| (path, n) -> begin
(

let path = (FStar_String.concat "_" path)
in if ((path = (FStar_ST.read current_module_name)) || (path = "")) then begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((n), (None)))
end else begin
(

let _82_56 = if (not ((let _179_38 = (FStar_ST.read export_modules)
in (FStar_List.existsb (fun x -> (x = path)) _179_38)))) then begin
(let _179_40 = (let _179_39 = (FStar_ST.read export_modules)
in (FStar_List.append ((path)::[]) _179_39))
in (FStar_ST.op_Colon_Equals export_modules _179_40))
end else begin
()
end
in FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat path (Prims.strcat "." n))), (None))))
end)
end))


let rec is_pure_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (p, le) -> begin
(not ((let _179_43 = (FStar_List.map is_pure_expr le)
in (FStar_List.contains false _179_43))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (le) -> begin
(not ((let _179_44 = (FStar_List.map is_pure_expr le)
in (FStar_List.contains false _179_44))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_75, lne) -> begin
(not ((let _179_46 = (FStar_List.map (fun _82_81 -> (match (_82_81) with
| (n, e) -> begin
(is_pure_expr e)
end)) lne)
in (FStar_List.contains false _179_46))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, le) -> begin
(not ((let _179_47 = (FStar_List.map is_pure_expr le)
in (FStar_List.contains false _179_47))))
end
| _82_87 -> begin
false
end))


let rec get_Generic : FStar_Extraction_JavaScript_Ast.typ  ->  Prims.string Prims.list = (fun t -> (match (t) with
| FStar_Extraction_JavaScript_Ast.JST_Generic (g, v) -> begin
(match (v) with
| Some (v1) -> begin
(FStar_List.collect get_Generic v1)
end
| None -> begin
(match (g) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _82_98) -> begin
if ((FStar_String.get id (Prims.parse_int "0")) = '\'') then begin
(id)::[]
end else begin
[]
end
end
| _82_102 -> begin
[]
end)
end)
end
| FStar_Extraction_JavaScript_Ast.JST_Function (_82_104, _82_106, gen_d) -> begin
(match (gen_d) with
| Some (v) -> begin
v
end
| None -> begin
[]
end)
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(FStar_List.collect get_Generic lt)
end
| FStar_Extraction_JavaScript_Ast.JST_Object (l, _82_117, _82_119) -> begin
(FStar_List.collect (fun _82_125 -> (match (_82_125) with
| (_82_123, t) -> begin
(get_Generic t)
end)) l)
end
| _82_127 -> begin
[]
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_129 -> (match (_82_129) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_138 = m
in (match (_82_138) with
| ((prefix, final), _82_135, _82_137) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_148 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (

let _82_150 = (FStar_ST.op_Colon_Equals export_modules [])
in (let _179_91 = (translate_module m)
in Some (_179_91))))
end)
with
| e -> begin
(

let _82_144 = (let _179_93 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_93))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_156 -> (match (_82_156) with
| (module_name, modul, _82_155) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let _82_162 = (FStar_ST.op_Colon_Equals current_module_name (FStar_String.concat "_" module_name))
in (

let res = (FStar_List.filter_map translate_decl decls)
in (

let create_module_exports = (

let require_f = (fun m -> FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("require"), (None)))), ((FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ((Prims.strcat "./" m))), (""))))::[]))))
in (let _179_102 = (let _179_100 = (let _179_98 = (FStar_ST.read export_modules)
in (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((m), (None)))), (Some ((require_f m)))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))) _179_98))
in (FStar_All.pipe_right _179_100 (fun _179_99 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_99))))
in (FStar_All.pipe_right _179_102 (fun _179_101 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_101)))))
in (FStar_List.append ((create_module_exports)::[]) res))))
end
| _82_170 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (_82_174, lfunc) -> begin
(

let for1 = (fun _82_187 -> (match (_82_187) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, _82_185); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = if (not (pt)) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some ([], ty) -> begin
(let _179_107 = (translate_type ty)
in (FStar_All.pipe_right _179_107 (fun _179_106 -> Some (_179_106))))
end
| Some (lp, ty) -> begin
(match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_199, t2) -> begin
(

let lp = (match (lp) with
| [] -> begin
None
end
| _82_205 -> begin
(let _179_110 = (FStar_List.map (fun _82_209 -> (match (_82_209) with
| (id, _82_208) -> begin
id
end)) lp)
in (FStar_All.pipe_right _179_110 (fun _179_109 -> Some (_179_109))))
end)
in if unit_b then begin
None
end else begin
(let _179_117 = (let _179_115 = (let _179_114 = (let _179_112 = (let _179_111 = (translate_type t1)
in (((("_1"), (None))), (_179_111)))
in (_179_112)::[])
in (let _179_113 = (translate_type t2)
in ((_179_114), (_179_113), (lp))))
in FStar_Extraction_JavaScript_Ast.JST_Function (_179_115))
in (FStar_All.pipe_right _179_117 (fun _179_116 -> Some (_179_116))))
end)
end
| _82_212 -> begin
None
end)
end)
end
in if (is_pure_expr expr) then begin
(let _179_123 = (let _179_122 = (let _179_121 = (let _179_120 = (let _179_119 = (let _179_118 = (translate_expr_pure expr)
in Some (_179_118))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (_179_119)))
in (_179_120)::[])
in ((_179_121), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_122))
in (_179_123)::[])
end else begin
(let _179_125 = (let _179_124 = (translate_expr expr ((name), (t)) None)
in (_179_124)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::_179_125)
end)
end))
in (let _179_131 = (let _179_129 = (let _179_127 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _179_127 (fun _179_126 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_126))))
in (FStar_All.pipe_right _179_129 (fun _179_128 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_128))))
in (FStar_All.pipe_right _179_131 (fun _179_130 -> Some (_179_130)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_215) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_218, name, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| _82_227 -> begin
(let _179_134 = (FStar_List.map (fun _82_231 -> (match (_82_231) with
| (id, _82_230) -> begin
id
end)) tparams)
in (FStar_All.pipe_right _179_134 (fun _179_133 -> Some (_179_133))))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _179_138 = (let _179_137 = (translate_type t)
in ((((name), (None))), (tparams), (_179_137)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_138))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _82_242 -> (match (_82_242) with
| (n, t) -> begin
(let _179_140 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_179_140)))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.mapi (fun i t -> (let _179_153 = (let _179_149 = (let _179_148 = (let _179_147 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_147))
in ((_179_148), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_149))
in (let _179_152 = (let _179_151 = (let _179_150 = (translate_type t)
in (_179_150)::[])
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_151))
in ((_179_153), (_179_152))))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_254 -> (match (_82_254) with
| (n, l) -> begin
(let _179_159 = (let _179_158 = (let _179_157 = (let _179_156 = (let _179_155 = (fields_t l)
in (FStar_List.append (tag n) _179_155))
in ((_179_156), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_157))
in ((((n), (None))), (tparams), (_179_158)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_159))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _179_162 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((x), (None)))), (None)))) t)
in (FStar_All.pipe_right _179_162 (fun _179_161 -> Some (_179_161))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun _82_263 -> (match (_82_263) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((n), (None)))), (tparams_gen)))
end)) lfields)
in (

let union_t = FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Union (lnames))))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append lfields_t ((union_t)::[])))))))))
end))
in (

let body_t = (match (body) with
| None -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty] with empty body")
end
| Some (v) -> begin
(forbody v)
end)
in (let _179_166 = (FStar_All.pipe_right body_t (fun _179_164 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_164)))
in (FStar_All.pipe_right _179_166 (fun _179_165 -> Some (_179_165)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_271) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_274) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _179_169 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block ([])) (fun _179_167 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_167)))
in (FStar_All.pipe_right _179_169 (fun _179_168 -> Some (_179_168))))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_281) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun e var stmt -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e) -> begin
(

let c = (let _179_175 = (let _179_174 = (let _179_173 = (translate_expr_pure e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_173)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_174))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_175))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((_82_292, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_299); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let c = if (is_pure_expr body) then begin
(let _179_183 = (let _179_180 = (let _179_179 = (let _179_178 = (let _179_177 = (let _179_176 = (translate_expr_pure body)
in Some (_179_176))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (_179_177)))
in (_179_178)::[])
in ((_179_179), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_180))
in (let _179_182 = (let _179_181 = (translate_expr continuation var stmt)
in (_179_181)::[])
in (_179_183)::_179_182))
end else begin
(let _179_187 = (let _179_186 = (let _179_185 = (let _179_184 = (translate_expr continuation var stmt)
in Some (_179_184))
in (translate_expr body ((name), (None)) _179_185))
in (_179_186)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_187)
end
in FStar_Extraction_JavaScript_Ast.JSS_Block (c))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_309) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let generic_t = (FStar_ST.alloc [])
in (

let addUnique = (fun lst -> (FStar_List.map (fun el -> if (not ((let _179_192 = (FStar_ST.read generic_t)
in (FStar_List.existsb (fun x -> (x = el)) _179_192)))) then begin
(let _179_194 = (let _179_193 = (FStar_ST.read generic_t)
in (FStar_List.append ((el)::[]) _179_193))
in (FStar_ST.op_Colon_Equals generic_t _179_194))
end else begin
()
end) lst))
in (

let args = (FStar_List.map (fun _82_325 -> (match (_82_325) with
| ((n, _82_322), t) -> begin
(

let t = (translate_type t)
in (

let _82_327 = (let _179_197 = (let _179_196 = (get_Generic t)
in (addUnique _179_196))
in (FStar_All.pipe_right _179_197 Prims.ignore))
in FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (Some (t))))))
end)) args)
in (

let generic_r = (match ((FStar_ST.read generic_t)) with
| [] -> begin
None
end
| _82_332 -> begin
(let _179_198 = (FStar_ST.read generic_t)
in Some (_179_198))
end)
in (

let body_t = if (is_pure_expr body) then begin
(let _179_199 = (translate_expr_pure body)
in FStar_Extraction_JavaScript_Ast.JS_BodyExpression (_179_199))
end else begin
(let _179_202 = (let _179_201 = (let _179_200 = (translate_expr body (("_res"), (None)) (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))))
in (_179_200)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_201)
in FStar_Extraction_JavaScript_Ast.JS_BodyBlock (_179_202))
end
in (

let ret_t = (match ((Prims.snd var)) with
| None -> begin
None
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (_82_339, t2, _82_342) -> begin
Some (t2)
end
| _82_346 -> begin
None
end)
end)
in (

let c = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (((None), (args), (body_t), (ret_t), (generic_r)))))))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))))))))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_82_353, path) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let s2 = (match (s2) with
| Some (v) -> begin
(let _179_203 = (translate_expr v var None)
in Some (_179_203))
end
| None -> begin
None
end)
in (

let c = if (is_pure_expr cond) then begin
(let _179_207 = (let _179_206 = (let _179_205 = (translate_expr_pure cond)
in (let _179_204 = (translate_expr s1 var None)
in ((_179_205), (_179_204), (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_206))
in (_179_207)::[])
end else begin
(let _179_213 = (let _179_212 = (let _179_211 = (let _179_210 = (let _179_209 = (let _179_208 = (translate_expr s1 var None)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (_179_208), (s2)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_209))
in Some (_179_210))
in (translate_expr cond (("_cond"), (None)) _179_211))
in (_179_212)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_213)
end
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_371) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_374) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(

let var = (let _179_215 = (let _179_214 = (translate_type in_e.FStar_Extraction_ML_Syntax.mlty)
in Some (_179_214))
in (((Prims.fst var)), (_179_215)))
in (translate_expr in_e var stmt))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let c = if (is_pure_expr e_in) then begin
(

let expr = (translate_expr_pure e_in)
in (let _179_216 = (translate_match lb expr var)
in (_179_216)::[]))
end else begin
(

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_match_e"), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (let _179_220 = (let _179_219 = (let _179_218 = (let _179_217 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_match_e"), (None)))) var)
in Some (_179_217))
in (translate_expr e_in (("_match_e"), (None)) _179_218))
in (_179_219)::[])
in (decl_v)::_179_220))
end
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(let _179_223 = (FStar_List.map (fun x -> (translate_expr x var None)) ls)
in (FStar_All.pipe_right _179_223 (fun _179_222 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_222))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let is_If = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_If (_)) | (FStar_Extraction_ML_Syntax.MLE_Match (_)) -> begin
true
end
| _82_409 -> begin
false
end))
in (

let args = (FStar_List.map (fun x -> if (is_If x) then begin
(

let fv_x = (FStar_Absyn_Util.gensym ())
in (

let _82_412 = (let _179_231 = (let _179_230 = (FStar_ST.read new_fv)
in (let _179_229 = (let _179_228 = (let _179_227 = (translate_expr x ((fv_x), (None)) None)
in (_179_227)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_228)
in (FStar_List.append _179_230 _179_229)))
in (FStar_ST.op_Colon_Equals new_fv _179_231))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None)))))
end else begin
(translate_expr_pure x)
end) args)
in (

let expr = (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_236 = (let _179_235 = (let _179_232 = (mk_op_bin op)
in (FStar_Util.must _179_232))
in (let _179_234 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_233 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_235), (_179_234), (_179_233)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_236))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_240 = (let _179_239 = (FStar_Util.must (mk_op_bool op))
in (let _179_238 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_237 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_239), (_179_238), (_179_237)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_240))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_244 = (let _179_243 = (let _179_241 = (mk_op_un op)
in (FStar_Util.must _179_241))
in (let _179_242 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_179_243), (_179_242))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_244))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(let _179_246 = (let _179_245 = (getName ((path), (function_name)))
in ((_179_245), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_246))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_436) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))
end
| _82_440 -> begin
(FStar_All.failwith "todo: translation [MLE_App]")
end)
in (

let expr_t = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (expr))))
in (let _179_248 = (let _179_247 = (FStar_ST.read new_fv)
in (FStar_List.append _179_247 ((expr_t)::[])))
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_248)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let is_If = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_If (_)) | (FStar_Extraction_ML_Syntax.MLE_Match (_)) -> begin
true
end
| _82_459 -> begin
false
end))
in (

let lexpr = (FStar_List.map (fun x -> if (is_If x) then begin
(

let fv_x = (FStar_Absyn_Util.gensym ())
in (

let _82_462 = (let _179_256 = (let _179_255 = (FStar_ST.read new_fv)
in (let _179_254 = (let _179_253 = (let _179_252 = (translate_expr x ((fv_x), (None)) None)
in (_179_252)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_253)
in (FStar_List.append _179_255 _179_254)))
in (FStar_ST.op_Colon_Equals new_fv _179_256))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None)))))
end else begin
(translate_expr_pure x)
end) lexpr)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_0"), (None)))), (FStar_Extraction_JavaScript_Ast.JSE_Array (Some (lexpr))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[])))))
in (let _179_258 = (let _179_257 = (FStar_ST.read new_fv)
in (FStar_List.append _179_257 ((expr)::[])))
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_258))))))
end
| _82_467 -> begin
FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("TOOOODo!"), (None))))
end))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_473) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
(getName ((path), (n)))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args_t = (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(match (c) with
| ("Nil") | ("None") -> begin
(let _179_263 = (let _179_262 = (translate_expr_pure x)
in (let _179_261 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_262), (_179_261))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_263))
end
| _82_494 -> begin
(translate_expr_pure x)
end)
end
| _82_496 -> begin
(translate_expr_pure x)
end)) args)
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_268 = (let _179_267 = (let _179_264 = (mk_op_bin op)
in (FStar_Util.must _179_264))
in (let _179_266 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_265 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_267), (_179_266), (_179_265)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_268))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_272 = (let _179_271 = (FStar_Util.must (mk_op_bool op))
in (let _179_270 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_269 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_271), (_179_270), (_179_269)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_272))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_276 = (let _179_275 = (let _179_273 = (mk_op_un op)
in (FStar_Util.must _179_273))
in (let _179_274 = (FStar_List.nth args_t (Prims.parse_int "0"))
in ((_179_275), (_179_274))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_276))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(let _179_278 = (let _179_277 = (getName ((path), (function_name)))
in ((_179_277), (args_t)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_278))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_519) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args_t)))
end
| _82_523 -> begin
(FStar_All.failwith "todo: translation [MLE_App]")
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let create_fields = (FStar_List.mapi (fun i x -> (let _179_286 = (let _179_285 = (let _179_283 = (let _179_282 = (let _179_281 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_281))
in ((_179_282), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_283))
in (let _179_284 = (translate_expr_pure x)
in ((_179_285), (_179_284), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_286))) lexp)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (FStar_List.length lexp)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _82_535 -> (match (_82_535) with
| (id, x) -> begin
(let _179_289 = (let _179_288 = (translate_expr_pure x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_288), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_289))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(let _179_296 = (let _179_295 = (let _179_294 = (let _179_293 = (let _179_292 = (let _179_291 = (let _179_290 = (FStar_List.map translate_expr_pure lexpr)
in Some (_179_290))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_291))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_0"), (None)))), (_179_292), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_293))
in (_179_294)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_295)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_296))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _82_545, _82_547) -> begin
(translate_expr_pure e)
end
| _82_551 -> begin
(FStar_All.failwith "todo: translation ml-expr-pure")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x var -> (match (lb) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end
| ((p, guard, expr_r))::tl -> begin
(let _179_301 = (translate_expr expr_r var None)
in (let _179_300 = (translate_match tl fv_x var)
in (translate_pat_guard ((p), (guard)) fv_x _179_301 _179_300)))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_564 fv_x s1 s2 -> (match (_82_564) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_307 = (let _179_306 = (translate_expr_pure v_guard)
in ((_179_306), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_307))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_578) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_315 = (let _179_314 = (let _179_313 = (let _179_312 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_312)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_313))
in ((_179_314), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_315))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((path, c), lp) -> begin
(

let if_true = (match (lp) with
| [] -> begin
s1
end
| (x)::[] -> begin
(translate_pat x (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_0"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) s1 s2)
end
| _82_594 -> begin
(translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_0"), (None))))))) s1 s2)
end)
in FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))), (if_true), (Some (s2)))))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (lp) -> begin
(translate_p_branch lp fv_x s1 s2)
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, lp) -> begin
(translate_p_record lp fv_x s1 s2)
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(translate_p_tuple lp (Prims.parse_int "0") fv_x s1 s2)
end))
and translate_p_ctor : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(translate_pat x fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_320 = (translate_p_ctor tl (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "1")))), ("")))))))) s1 s2)
in (translate_pat hd (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) _179_320 s2))
end
| [] -> begin
(FStar_All.failwith "Empty list in pattern matching")
end))
and translate_p_tuple : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp d fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(let _179_331 = (let _179_330 = (let _179_329 = (let _179_328 = (let _179_327 = (let _179_326 = (FStar_Util.string_of_int d)
in (Prims.strcat "_" _179_326))
in ((_179_327), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_328))
in ((fv_x), (_179_329)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_330))
in (translate_pat x _179_331 s1 s2))
end
| (hd)::tl -> begin
(let _179_338 = (let _179_336 = (let _179_335 = (let _179_334 = (let _179_333 = (let _179_332 = (FStar_Util.string_of_int d)
in (Prims.strcat "_" _179_332))
in ((_179_333), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_334))
in ((fv_x), (_179_335)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_336))
in (let _179_337 = (translate_p_tuple tl (d + (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat hd _179_338 _179_337 s2)))
end
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_tuple")
end))
and translate_p_record : (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlpattern) Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(translate_pat (Prims.snd x) (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" (Prims.fst x))), (None))))))) s1 s2)
end
| (hd)::tl -> begin
(let _179_343 = (translate_p_record tl fv_x s1 s2)
in (translate_pat (Prims.snd hd) (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" (Prims.fst hd))), (None))))))) _179_343 s2))
end
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_record")
end))
and translate_p_branch : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(translate_pat x fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_348 = (translate_p_branch tl fv_x s1 s2)
in (translate_pat hd fv_x s1 _179_348))
end
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_branch")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, _82_651) -> begin
(let _179_353 = (let _179_352 = (let _179_351 = (let _179_350 = (FStar_Util.int_of_string s)
in (float_of_int _179_350))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_351))
in ((_179_352), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_353))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_657) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_662) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _82_670) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((id), (None)))), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _179_355 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_355))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_677, t2) -> begin
(

let t1_t = (translate_type t1)
in (

let t2_t = (translate_type t2)
in (

let generic_t = (FStar_ST.alloc [])
in (

let addUnique = (fun lst -> (FStar_List.map (fun el -> if (not ((let _179_360 = (FStar_ST.read generic_t)
in (FStar_List.existsb (fun x -> (x = el)) _179_360)))) then begin
(let _179_362 = (let _179_361 = (FStar_ST.read generic_t)
in (FStar_List.append ((el)::[]) _179_361))
in (FStar_ST.op_Colon_Equals generic_t _179_362))
end else begin
()
end) lst))
in (

let _82_688 = (let _179_364 = (let _179_363 = (get_Generic t1_t)
in (addUnique _179_363))
in (FStar_All.pipe_right _179_364 Prims.ignore))
in (

let _82_690 = (let _179_366 = (let _179_365 = (get_Generic t2_t)
in (addUnique _179_365))
in (FStar_All.pipe_right _179_366 Prims.ignore))
in (

let generic_r = (match ((FStar_ST.read generic_t)) with
| [] -> begin
None
end
| _82_694 -> begin
(let _179_367 = (FStar_ST.read generic_t)
in Some (_179_367))
end)
in FStar_Extraction_JavaScript_Ast.JST_Function (((((((("_1"), (None))), (t1_t)))::[]), (t2_t), (generic_r))))))))))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _179_368 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _179_368)) then begin
(

let args = (FStar_List.mapi (fun i x -> (let _179_375 = (let _179_373 = (let _179_372 = (let _179_371 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_371))
in ((_179_372), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_373))
in (let _179_374 = (translate_type x)
in ((_179_375), (_179_374))))) args)
in (

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Tuple"), (""))))))::[]
in (

let arity = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_NumberLiteral ((((float_of_int (FStar_List.length args))), (""))))))::[]
in FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag (FStar_List.append arity args))), ([]), ([]))))))
end else begin
(

let args = (match (args) with
| [] -> begin
None
end
| _82_709 -> begin
(let _179_377 = (FStar_List.map translate_type args)
in (FStar_All.pipe_right _179_377 (fun _179_376 -> Some (_179_376))))
end)
in FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((name), (None)))), (args))))
end
end
end))




