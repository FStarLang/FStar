
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
(FStar_All.failwith "todo: translation [:=] for mutable variables")
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
(FStar_All.failwith "todo: translation [!] for mutable variables")
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
| FStar_Extraction_ML_Syntax.MLE_Fun (largs, e) -> begin
(is_pure_expr e)
end
| _82_91 -> begin
false
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_93 -> (match (_82_93) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_102 = m
in (match (_82_102) with
| ((prefix, final), _82_99, _82_101) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_112 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _179_88 = (translate_module m)
in Some (_179_88)))
end)
with
| e -> begin
(

let _82_108 = (let _179_90 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_90))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_118 -> (match (_82_118) with
| (module_name, modul, _82_117) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let _82_124 = (FStar_ST.op_Colon_Equals current_module_name (FStar_String.concat "_" module_name))
in (

let res = (FStar_List.filter_map translate_decl decls)
in (

let create_module_exports = (

let require_f = (fun m -> FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("require"), (None)))), ((FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ((Prims.strcat "./" m))), (""))))::[]))))
in (let _179_99 = (let _179_97 = (let _179_95 = (FStar_ST.read export_modules)
in (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((m), (None)))), (Some ((require_f m)))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))) _179_95))
in (FStar_All.pipe_right _179_97 (fun _179_96 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_96))))
in (FStar_All.pipe_right _179_99 (fun _179_98 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_98)))))
in (FStar_List.append ((create_module_exports)::[]) res))))
end
| _82_132 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (_82_136, lfunc) -> begin
(

let for1 = (fun _82_150 -> (match (_82_150) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, _82_148); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _82_144; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = if (not (pt)) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some ([], ty) -> begin
(let _179_104 = (translate_type ty)
in (FStar_All.pipe_right _179_104 (fun _179_103 -> Some (_179_103))))
end
| Some ((_82_159)::_82_157, ty) -> begin
None
end)
end
in if (is_pure_expr expr) then begin
(let _179_110 = (let _179_109 = (let _179_108 = (let _179_107 = (let _179_106 = (let _179_105 = (translate_expr_pure expr)
in Some (_179_105))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (_179_106)))
in (_179_107)::[])
in ((_179_108), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_109))
in (_179_110)::[])
end else begin
(

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in (let _179_112 = (let _179_111 = (translate_expr expr ((name), (None)) None)
in (_179_111)::[])
in (decl_v)::_179_112))
end)
end))
in (let _179_118 = (let _179_116 = (let _179_114 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _179_114 (fun _179_113 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_113))))
in (FStar_All.pipe_right _179_116 (fun _179_115 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_115))))
in (FStar_All.pipe_right _179_118 (fun _179_117 -> Some (_179_117)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_167) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_170, name, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| _82_179 -> begin
(let _179_121 = (FStar_List.map (fun _82_183 -> (match (_82_183) with
| (id, _82_182) -> begin
id
end)) tparams)
in (FStar_All.pipe_right _179_121 (fun _179_120 -> Some (_179_120))))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _179_125 = (let _179_124 = (translate_type t)
in ((((name), (None))), (tparams), (_179_124)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_125))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _82_194 -> (match (_82_194) with
| (n, t) -> begin
(let _179_127 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_179_127)))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.mapi (fun i t -> (let _179_140 = (let _179_136 = (let _179_135 = (let _179_134 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_134))
in ((_179_135), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_136))
in (let _179_139 = (let _179_138 = (let _179_137 = (translate_type t)
in (_179_137)::[])
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_138))
in ((_179_140), (_179_139))))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_206 -> (match (_82_206) with
| (n, l) -> begin
(let _179_146 = (let _179_145 = (let _179_144 = (let _179_143 = (let _179_142 = (fields_t l)
in (FStar_List.append (tag n) _179_142))
in ((_179_143), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_144))
in ((((n), (None))), (tparams), (_179_145)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_146))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _179_149 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((x), (None)))), (None)))) t)
in (FStar_All.pipe_right _179_149 (fun _179_148 -> Some (_179_148))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun _82_215 -> (match (_82_215) with
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
in (let _179_153 = (FStar_All.pipe_right body_t (fun _179_151 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_151)))
in (FStar_All.pipe_right _179_153 (fun _179_152 -> Some (_179_152)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_223) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_226) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _179_156 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block ([])) (fun _179_154 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_154)))
in (FStar_All.pipe_right _179_156 (fun _179_155 -> Some (_179_155))))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_233) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun e var stmt -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e) -> begin
(

let c = (let _179_162 = (let _179_161 = (let _179_160 = (translate_expr_pure e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_160)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_161))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_162))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((_82_244, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_251); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let c = if (is_pure_expr body) then begin
(let _179_170 = (let _179_167 = (let _179_166 = (let _179_165 = (let _179_164 = (let _179_163 = (translate_expr_pure body)
in Some (_179_163))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (_179_164)))
in (_179_165)::[])
in ((_179_166), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_167))
in (let _179_169 = (let _179_168 = (translate_expr continuation var stmt)
in (_179_168)::[])
in (_179_170)::_179_169))
end else begin
(let _179_174 = (let _179_173 = (let _179_172 = (let _179_171 = (translate_expr continuation var stmt)
in Some (_179_171))
in (translate_expr body ((name), (None)) _179_172))
in (_179_173)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_174)
end
in FStar_Extraction_JavaScript_Ast.JSS_Block (c))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_261) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args = (FStar_List.map (fun _82_272 -> (match (_82_272) with
| ((n, _82_269), t) -> begin
FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (None)))
end)) args)
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let body_t = (translate_expr body (("_res"), (None)) (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))))
in (

let c = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (((None), (args), (FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((decl_v)::(body_t)::[])), (None), (None)))))))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_82_281, path) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let s2 = (match (s2) with
| Some (v) -> begin
(let _179_176 = (translate_expr v var None)
in Some (_179_176))
end
| None -> begin
None
end)
in (

let c = if (is_pure_expr cond) then begin
(let _179_180 = (let _179_179 = (let _179_178 = (translate_expr_pure cond)
in (let _179_177 = (translate_expr s1 var None)
in ((_179_178), (_179_177), (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_179))
in (_179_180)::[])
end else begin
(let _179_186 = (let _179_185 = (let _179_184 = (let _179_183 = (let _179_182 = (let _179_181 = (translate_expr s1 var None)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (_179_181), (s2)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_182))
in Some (_179_183))
in (translate_expr cond (("_cond"), (None)) _179_184))
in (_179_185)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_186)
end
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append c ((v)::[])))
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block (c)
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_299) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_302) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(

let var = (let _179_188 = (let _179_187 = (translate_type t_to)
in Some (_179_187))
in (((Prims.fst var)), (_179_188)))
in (translate_expr in_e var stmt))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let c = if (is_pure_expr e_in) then begin
(

let expr = (translate_expr_pure e_in)
in (let _179_189 = (translate_match lb expr var)
in (_179_189)::[]))
end else begin
(

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_match_e"), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (let _179_193 = (let _179_192 = (let _179_191 = (let _179_190 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_match_e"), (None)))) var)
in Some (_179_190))
in (translate_expr e_in (("_match_e"), (None)) _179_191))
in (_179_192)::[])
in (decl_v)::_179_193))
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
(

let lastIn = (FStar_List.length ls)
in (let _179_199 = (FStar_List.mapi (fun i x -> if (i = (lastIn - (Prims.parse_int "1"))) then begin
(translate_expr x var None)
end else begin
(let _179_197 = (translate_expr_pure x)
in (FStar_All.pipe_right _179_197 (fun _179_196 -> FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_196))))
end) ls)
in (FStar_All.pipe_right _179_199 (fun _179_198 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_198)))))
end
| _82_326 -> begin
(let _179_202 = (let _179_201 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("TODO!!"), (None)))) (fun _179_200 -> FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_200)))
in (_179_201)::[])
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_202))
end))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_332) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
(getName ((path), (n)))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args_t = (FStar_List.map translate_expr_pure args)
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_208 = (let _179_207 = (let _179_204 = (mk_op_bin op)
in (FStar_Util.must _179_204))
in (let _179_206 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_205 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_207), (_179_206), (_179_205)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_208))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_212 = (let _179_211 = (FStar_Util.must (mk_op_bool op))
in (let _179_210 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_209 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_211), (_179_210), (_179_209)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_212))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_216 = (let _179_215 = (let _179_213 = (mk_op_un op)
in (FStar_Util.must _179_213))
in (let _179_214 = (FStar_List.nth args_t (Prims.parse_int "0"))
in ((_179_215), (_179_214))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_216))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(let _179_218 = (let _179_217 = (getName ((path), (function_name)))
in ((_179_217), (args_t)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_218))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_365) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args_t)))
end
| _82_369 -> begin
(FStar_All.failwith "todo: translation [MLE_App]")
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let create_fields = (FStar_List.mapi (fun i x -> (let _179_226 = (let _179_225 = (let _179_223 = (let _179_222 = (let _179_221 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_221))
in ((_179_222), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_223))
in (let _179_224 = (translate_expr_pure x)
in ((_179_225), (_179_224), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_226))) lexp)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (FStar_List.length lexp)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _82_381 -> (match (_82_381) with
| (id, x) -> begin
(let _179_229 = (let _179_228 = (translate_expr_pure x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_228), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_229))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(let _179_236 = (let _179_235 = (let _179_234 = (let _179_233 = (let _179_232 = (let _179_231 = (let _179_230 = (FStar_List.map translate_expr_pure lexpr)
in Some (_179_230))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_231))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_232), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_233))
in (_179_234)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_235)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_236))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args = (FStar_List.map (fun _82_398 -> (match (_82_398) with
| ((n, _82_395), t) -> begin
FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (None)))
end)) args)
in (let _179_240 = (let _179_239 = (let _179_238 = (translate_expr_pure body)
in FStar_Extraction_JavaScript_Ast.JS_BodyExpression (_179_238))
in ((None), (args), (_179_239), (None), (None)))
in FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_179_240)))
end
| _82_401 -> begin
(FStar_All.failwith "It\'s not a pure expression!")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x var -> (match (lb) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end
| ((p, guard, expr_r))::tl -> begin
(let _179_245 = (translate_expr expr_r var None)
in (let _179_244 = (translate_match tl fv_x var)
in (translate_pat_guard ((p), (guard)) fv_x _179_245 _179_244)))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_414 fv_x s1 s2 -> (match (_82_414) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_251 = (let _179_250 = (translate_expr_pure v_guard)
in ((_179_250), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_251))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_428) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_259 = (let _179_258 = (let _179_257 = (let _179_256 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_256)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_257))
in ((_179_258), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_259))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((path, c), lp) -> begin
(

let if_true = (match (lp) with
| [] -> begin
s1
end
| (x)::[] -> begin
(translate_pat x (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) s1 s2)
end
| _82_444 -> begin
(translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None))))))) s1 s2)
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
(let _179_264 = (translate_p_ctor tl (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "1")))), ("")))))))) s1 s2)
in (translate_pat hd (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) _179_264 s2))
end
| [] -> begin
(FStar_All.failwith "Empty list in pattern matching")
end))
and translate_p_tuple : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp d fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(let _179_275 = (let _179_274 = (let _179_273 = (let _179_272 = (let _179_271 = (let _179_270 = (FStar_Util.string_of_int d)
in (Prims.strcat "_" _179_270))
in ((_179_271), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_272))
in ((fv_x), (_179_273)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_274))
in (translate_pat x _179_275 s1 s2))
end
| (hd)::tl -> begin
(let _179_282 = (let _179_280 = (let _179_279 = (let _179_278 = (let _179_277 = (let _179_276 = (FStar_Util.string_of_int d)
in (Prims.strcat "_" _179_276))
in ((_179_277), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_278))
in ((fv_x), (_179_279)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_280))
in (let _179_281 = (translate_p_tuple tl (d + (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat hd _179_282 _179_281 s2)))
end
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_tuple")
end))
and translate_p_record : (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlpattern) Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(translate_pat (Prims.snd x) (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" (Prims.fst x))), (None))))))) s1 s2)
end
| (hd)::tl -> begin
(let _179_287 = (translate_p_record tl fv_x s1 s2)
in (translate_pat (Prims.snd hd) (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" (Prims.fst hd))), (None))))))) _179_287 s2))
end
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_record")
end))
and translate_p_branch : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(translate_pat x fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_292 = (translate_p_branch tl fv_x s1 s2)
in (translate_pat hd fv_x s1 _179_292))
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
| FStar_Extraction_ML_Syntax.MLC_Int (s, _82_501) -> begin
(let _179_297 = (let _179_296 = (let _179_295 = (let _179_294 = (FStar_Util.int_of_string s)
in (float_of_int _179_294))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_295))
in ((_179_296), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_297))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_507) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_512) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _82_520) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((id), (None)))), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _179_299 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_299))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_527, t2) -> begin
(

let t1_t = (translate_type t1)
in (

let t2_t = (translate_type t2)
in FStar_Extraction_JavaScript_Ast.JST_Function (((((((("_1"), (None))), (t1_t)))::[]), (t2_t), (None)))))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _179_300 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _179_300)) then begin
(

let args = (FStar_List.mapi (fun i x -> (let _179_307 = (let _179_305 = (let _179_304 = (let _179_303 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_303))
in ((_179_304), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_305))
in (let _179_306 = (translate_type x)
in ((_179_307), (_179_306))))) args)
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
| _82_546 -> begin
(let _179_309 = (FStar_List.map translate_type args)
in (FStar_All.pipe_right _179_309 (fun _179_308 -> Some (_179_308))))
end)
in FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((name), (None)))), (args))))
end
end
end))




