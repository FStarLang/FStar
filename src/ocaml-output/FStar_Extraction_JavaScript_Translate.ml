
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
| "op_Bang" -> begin
(FStar_All.failwith "todo: translation [!]")
end
| _82_32 -> begin
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
| _82_38 -> begin
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
| _82_47 -> begin
None
end))


let is_standart_type : Prims.string  ->  Prims.bool = (fun t -> ((mk_standart_type t) <> None))


let is_prim_constructors : Prims.string  ->  Prims.bool = (fun s -> (FStar_List.existsb (fun x -> (x = s)) (("Cons")::("Nil")::("Some")::("None")::[])))


let float_of_int : Prims.int  ->  FStar_BaseTypes.float = (fun i -> (FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)))


let export_modules : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let current_module_name : Prims.string FStar_ST.ref = (FStar_ST.alloc "")


let lp_generic : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let getName = (fun _82_54 -> (match (_82_54) with
| (path, n) -> begin
(

let path = (FStar_String.concat "_" path)
in if ((path = (FStar_ST.read current_module_name)) || (path = "")) then begin
((n), (None))
end else begin
(

let _82_57 = if (not ((let _179_40 = (FStar_ST.read export_modules)
in (FStar_List.existsb (fun x -> (x = path)) _179_40)))) then begin
(let _179_42 = (let _179_41 = (FStar_ST.read export_modules)
in (FStar_List.append ((path)::[]) _179_41))
in (FStar_ST.op_Colon_Equals export_modules _179_42))
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
| FStar_Extraction_ML_Syntax.MLE_Var (n, _82_69) -> begin
(n <> (Prims.fst var))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, _82_74) -> begin
(is_pure_expr expr var)
end
| FStar_Extraction_ML_Syntax.MLE_CTor (p, le) -> begin
(not ((let _179_46 = (FStar_List.map (fun x -> (is_pure_expr x var)) le)
in (FStar_List.contains false _179_46))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (le) -> begin
(not ((let _179_48 = (FStar_List.map (fun x -> (is_pure_expr x var)) le)
in (FStar_List.contains false _179_48))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_86, lne) -> begin
(not ((let _179_50 = (FStar_List.map (fun _82_92 -> (match (_82_92) with
| (n, e) -> begin
(is_pure_expr e var)
end)) lne)
in (FStar_List.contains false _179_50))))
end
| FStar_Extraction_ML_Syntax.MLE_App (_82_94, args) -> begin
(not ((let _179_52 = (FStar_List.map (fun x -> (is_pure_expr x var)) args)
in (FStar_List.contains false _179_52))))
end
| _82_100 -> begin
false
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_102 -> (match (_82_102) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_111 = m
in (match (_82_111) with
| ((prefix, final), _82_108, _82_110) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_121 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (

let _82_123 = (FStar_ST.op_Colon_Equals export_modules [])
in (let _179_82 = (translate_module m)
in Some (_179_82))))
end)
with
| e -> begin
(

let _82_117 = (let _179_84 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_84))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_129 -> (match (_82_129) with
| (module_name, modul, _82_128) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let _82_135 = (FStar_ST.op_Colon_Equals current_module_name (FStar_String.concat "_" module_name))
in (

let res = (FStar_List.filter_map translate_decl decls)
in (

let create_module_imports = (let _179_91 = (let _179_89 = (let _179_87 = (FStar_ST.read export_modules)
in (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (((m), (None)))) _179_87))
in (FStar_All.pipe_right _179_89 (fun _179_88 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_88))))
in (FStar_All.pipe_right _179_91 (fun _179_90 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_90))))
in (FStar_List.append ((create_module_imports)::[]) res))))
end
| _82_141 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (_82_145, c_flag, lfunc) -> begin
(

let for1 = (fun _82_159 -> (match (_82_159) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, _82_157); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = (

let _82_160 = (FStar_ST.op_Colon_Equals lp_generic [])
in if ((not (pt)) || unit_b) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some (lp, ty) -> begin
(

let _82_171 = (let _179_96 = (FStar_List.map (fun _82_170 -> (match (_82_170) with
| (id, _82_169) -> begin
id
end)) lp)
in (FStar_ST.op_Colon_Equals lp_generic _179_96))
in (let _179_98 = (translate_type ty)
in (FStar_All.pipe_right _179_98 (fun _179_97 -> Some (_179_97)))))
end)
end)
in (

let is_private = (FStar_List.contains FStar_Extraction_ML_Syntax.Private c_flag)
in (

let c = if (is_pure_expr expr ((name), (None))) then begin
(let _179_103 = (let _179_102 = (let _179_101 = (let _179_100 = (let _179_99 = (translate_expr_pure expr)
in Some (_179_99))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (_179_100)))
in ((_179_101), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_102))
in (_179_103)::[])
end else begin
(translate_expr expr ((name), (t)) None)
end
in if is_private then begin
c
end else begin
(FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (FStar_Extraction_JavaScript_Ast.JSS_Block (c))), (FStar_Extraction_JavaScript_Ast.ExportValue))))::[]
end)))
end))
in (let _179_109 = (let _179_107 = (let _179_105 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _179_105 (fun _179_104 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_104))))
in (FStar_All.pipe_right _179_107 (fun _179_106 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_106))))
in (FStar_All.pipe_right _179_109 (fun _179_108 -> Some (_179_108)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_177) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_180, name, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| _82_189 -> begin
(let _179_112 = (FStar_List.map (fun _82_193 -> (match (_82_193) with
| (id, _82_192) -> begin
id
end)) tparams)
in (FStar_All.pipe_right _179_112 (fun _179_111 -> Some (_179_111))))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _179_116 = (let _179_115 = (translate_type t)
in ((((name), (None))), (tparams), (_179_115)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_116))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _82_204 -> (match (_82_204) with
| (n, t) -> begin
(let _179_118 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_179_118)))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.mapi (fun i t -> (let _179_129 = (let _179_127 = (let _179_126 = (let _179_125 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_125))
in ((_179_126), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_127))
in (let _179_128 = (translate_type t)
in ((_179_129), (_179_128))))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_216 -> (match (_82_216) with
| (n, l) -> begin
(let _179_135 = (let _179_134 = (let _179_133 = (let _179_132 = (let _179_131 = (fields_t l)
in (FStar_List.append (tag n) _179_131))
in ((_179_132), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_133))
in ((((n), (None))), (tparams), (_179_134)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_135))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _179_138 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((x), (None)))), (None)))) t)
in (FStar_All.pipe_right _179_138 (fun _179_137 -> Some (_179_137))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun _82_225 -> (match (_82_225) with
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
in (let _179_142 = (FStar_All.pipe_right body_t (fun _179_140 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_140)))
in (FStar_All.pipe_right _179_142 (fun _179_141 -> Some (_179_141)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_233) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_236) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _179_145 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block ([])) (fun _179_143 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_143)))
in (FStar_All.pipe_right _179_145 (fun _179_144 -> Some (_179_144))))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_243) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.list Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.list = (fun e var lstmt -> (

let get_res = (fun expr new_fv -> (

let lstmt = (match (lstmt) with
| Some (v) -> begin
v
end
| None -> begin
[]
end)
in (

let expr = if (((Prims.fst var) = "_res") || ((Prims.fst var) = "_match_e")) then begin
(FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (expr)))))::[]
end else begin
(FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (expr)))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]
end
in (let _179_153 = (FStar_ST.read new_fv)
in (FStar_List.append _179_153 ((FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append expr lstmt)))::[]))))))
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e var) -> begin
(

let c = (let _179_156 = (let _179_155 = (let _179_154 = (translate_expr_pure e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_154)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_155))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_156))
in (match (lstmt) with
| Some (v) -> begin
(FStar_List.append ((c)::[]) v)
end
| None -> begin
(c)::[]
end))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((_82_262, _82_264, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_271); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let c = (translate_expr continuation var lstmt)
in if (is_pure_expr body ((name), (None))) then begin
(let _179_162 = (let _179_161 = (let _179_160 = (let _179_159 = (let _179_158 = (let _179_157 = (translate_expr_pure body)
in Some (_179_157))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (_179_158)))
in ((_179_159), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_160))
in (_179_161)::[])
in (FStar_List.append _179_162 ((FStar_Extraction_JavaScript_Ast.JSS_Block (c))::[])))
end else begin
(translate_expr body ((name), (None)) (Some (c)))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_281) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args = (FStar_List.map (fun _82_292 -> (match (_82_292) with
| ((n, _82_289), t) -> begin
(let _179_166 = (let _179_165 = (let _179_164 = (translate_type t)
in Some (_179_164))
in ((n), (_179_165)))
in FStar_Extraction_JavaScript_Ast.JGP_Identifier (_179_166))
end)) args)
in (

let generic_t = (match ((FStar_ST.read lp_generic)) with
| [] -> begin
None
end
| _82_296 -> begin
(let _179_167 = (FStar_ST.read lp_generic)
in Some (_179_167))
end)
in (

let body_t = if (is_pure_expr body var) then begin
(let _179_168 = (translate_expr_pure body)
in FStar_Extraction_JavaScript_Ast.JS_BodyExpression (_179_168))
end else begin
(let _179_170 = (let _179_169 = (translate_expr body (("_res"), (None)) (Some ((FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))::[])))
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _179_169))
in FStar_Extraction_JavaScript_Ast.JS_BodyBlock (_179_170))
end
in (

let ret_t = (match ((Prims.snd var)) with
| None -> begin
None
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (_82_303, t2, _82_306) -> begin
Some (t2)
end
| _82_310 -> begin
None
end)
end)
in (

let c = (let _179_174 = (let _179_173 = (let _179_172 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (((None), (args), (body_t), (ret_t), (generic_t)))) (fun _179_171 -> Some (_179_171)))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((((Prims.fst var)), (None)))), (_179_172)))
in ((_179_173), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_174))
in (match (lstmt) with
| Some (v) -> begin
(FStar_List.append ((c)::[]) v)
end
| None -> begin
(c)::[]
end))))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let s2 = (match (s2) with
| Some (v) -> begin
(let _179_176 = (let _179_175 = (translate_expr v var None)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_175))
in Some (_179_176))
end
| None -> begin
None
end)
in (

let c = if (is_pure_expr cond var) then begin
(let _179_181 = (let _179_180 = (let _179_179 = (translate_expr_pure cond)
in (let _179_178 = (let _179_177 = (translate_expr s1 var None)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_177))
in ((_179_179), (_179_178), (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_180))
in (_179_181)::[])
end else begin
(let _179_188 = (let _179_187 = (let _179_186 = (let _179_185 = (let _179_184 = (let _179_183 = (let _179_182 = (translate_expr s1 var None)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_182))
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (_179_183), (s2)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_184))
in (_179_185)::[])
in Some (_179_186))
in (translate_expr cond (("_cond"), (None)) _179_187))
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _179_188))
end
in (

let c = if (((Prims.fst var) = "_res") || ((Prims.fst var) = "_match_e")) then begin
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
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_331) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_334) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(

let var = (let _179_190 = (let _179_189 = (translate_type in_e.FStar_Extraction_ML_Syntax.mlty)
in Some (_179_189))
in (((Prims.fst var)), (_179_190)))
in (translate_expr in_e var lstmt))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let c = if (is_pure_expr e_in var) then begin
(let _179_198 = (let _179_195 = (let _179_194 = (let _179_193 = (let _179_192 = (let _179_191 = (translate_expr_pure e_in)
in Some (_179_191))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_match_e"), (None)))), (_179_192)))
in ((_179_193), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_194))
in (_179_195)::[])
in (let _179_197 = (let _179_196 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_match_e"), (None)))) var)
in (_179_196)::[])
in (FStar_List.append _179_198 _179_197)))
end else begin
(let _179_202 = (let _179_201 = (let _179_200 = (let _179_199 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_match_e"), (None)))) var)
in (_179_199)::[])
in Some (_179_200))
in (translate_expr e_in (("_match_e"), (None)) _179_201))
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_match_e"), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::[]) _179_202))
end
in (

let c = if (((Prims.fst var) = "_res") || ((Prims.fst var) = "_match_e")) then begin
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
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(

let rec translate_seq = (fun l -> (match (l) with
| [] -> begin
(FStar_All.failwith "Empty list in [MLE_Seq]")
end
| (x)::[] -> begin
(translate_expr x var None)
end
| (hd)::tl -> begin
(let _179_206 = (let _179_205 = (translate_seq tl)
in Some (_179_205))
in (translate_expr hd (("_"), (None)) _179_206))
end))
in (

let c = (translate_seq ls)
in (

let c = if (((Prims.fst var) = "_res") || ((Prims.fst var) = "_match_e")) then begin
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
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let args = (create_pure_args new_fv args var)
in (

let expr = (translate_arg_app e args var)
in (get_res expr new_fv))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), lexpr) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let lexpr = (create_pure_args new_fv lexpr var)
in (

let expr = (match (c) with
| x when (is_prim_constructors x) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat "Prims._mk_" c)), (None)))), (lexpr)))
end
| _82_383 -> begin
(let _179_215 = (let _179_214 = (FStar_List.mapi (fun i x -> (let _179_213 = (let _179_212 = (let _179_211 = (let _179_210 = (let _179_209 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_209))
in ((_179_210), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_211))
in ((_179_212), (x), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_213))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _179_214))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_215))
end)
in (get_res expr new_fv))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.map (fun _82_394 -> (match (_82_394) with
| (id, x) -> begin
(let _179_219 = (let _179_218 = (let _179_217 = (create_pure_args new_fv ((x)::[]) var)
in (FStar_List.nth _179_217 (Prims.parse_int "0")))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_218), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_219))
end)) fields)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))
in (get_res expr new_fv))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.map (fun x -> (let _179_221 = (create_pure_args new_fv ((x)::[]) var)
in (FStar_List.nth _179_221 (Prims.parse_int "0")))) lexp)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSE_Array (Some (create_fields))
in (get_res expr new_fv))))
end
| _82_404 -> begin
(FStar_All.failwith "todo: translation ml-expr")
end)))
and create_pure_args : FStar_Extraction_JavaScript_Ast.statement_t Prims.list FStar_ST.ref  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list = (fun new_fv args var -> (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _82_413) when ((c = "Nil") || (c = "None")) -> begin
(let _179_228 = (let _179_227 = (translate_expr_pure x)
in (let _179_226 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_227), (_179_226))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_228))
end
| _82_417 -> begin
if (is_pure_expr x var) then begin
(translate_expr_pure x)
end else begin
(

let fv_x = (FStar_Absyn_Util.gensym ())
in (

let c = (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (_82_420) -> begin
(let _179_233 = (let _179_232 = (let _179_231 = (let _179_230 = (let _179_229 = (translate_expr_pure x)
in Some (_179_229))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (_179_230)))
in ((_179_231), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_232))
in (_179_233)::[])
end
| _82_423 -> begin
(translate_expr x ((fv_x), (None)) None)
end)
in (

let _82_425 = (let _179_235 = (let _179_234 = (FStar_ST.read new_fv)
in (FStar_List.append _179_234 c))
in (FStar_ST.op_Colon_Equals new_fv _179_235))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None))))))
end
end)) args))
and translate_arg_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e args var -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_242 = (let _179_241 = (FStar_Util.must (mk_op_bin op))
in (let _179_240 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_239 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_241), (_179_240), (_179_239)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_242))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_246 = (let _179_245 = (FStar_Util.must (mk_op_bool op))
in (let _179_244 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_243 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_245), (_179_244), (_179_243)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_246))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_250 = (let _179_249 = (let _179_247 = (mk_op_un op)
in (FStar_Util.must _179_247))
in (let _179_248 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_179_249), (_179_248))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_250))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(let _179_253 = (let _179_252 = (let _179_251 = (getName ((path), (function_name)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_251))
in ((_179_252), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_253))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_451) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))
end
| _82_455 -> begin
if (is_pure_expr e var) then begin
(let _179_255 = (let _179_254 = (translate_expr_pure e)
in ((_179_254), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_255))
end else begin
(FStar_All.failwith "todo: translation [MLE_App]")
end
end))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_461) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
(let _179_257 = (getName ((path), (n)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_257))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(let _179_259 = (let _179_258 = (FStar_List.map translate_expr_pure lexp)
in Some (_179_258))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_259))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _82_476 -> (match (_82_476) with
| (id, x) -> begin
(let _179_262 = (let _179_261 = (translate_expr_pure x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_261), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_262))
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
(let _179_270 = (let _179_269 = (let _179_267 = (let _179_266 = (let _179_265 = (let _179_264 = (let _179_263 = (translate_expr_pure hd)
in (_179_263)::[])
in Some (_179_264))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_265))
in ((_179_266), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("concat"), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_267))
in (let _179_268 = (FStar_List.map translate_expr_pure tl)
in ((_179_269), (_179_268))))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_270))
end)
end
| x when (is_prim_constructors x) -> begin
(let _179_272 = (let _179_271 = (FStar_List.map translate_expr_pure lexpr)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat "Prims._mk_" c)), (None)))), (_179_271)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_272))
end
| _82_491 -> begin
(let _179_282 = (let _179_281 = (FStar_List.mapi (fun i x -> (let _179_280 = (let _179_279 = (let _179_277 = (let _179_276 = (let _179_275 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_275))
in ((_179_276), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_277))
in (let _179_278 = (translate_expr_pure x)
in ((_179_279), (_179_278), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_280))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _179_281))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_282))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _82_496, _82_498) -> begin
(translate_expr_pure e)
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args = (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _82_510) when ((c = "Nil") || (c = "None")) -> begin
(let _179_286 = (let _179_285 = (translate_expr_pure x)
in (let _179_284 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_285), (_179_284))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_286))
end
| _82_514 -> begin
(translate_expr_pure x)
end)) args)
in (translate_arg_app e args ((""), (None))))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, (path, name)) -> begin
(let _179_288 = (let _179_287 = (translate_expr_pure expr)
in ((_179_287), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" name)), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_288))
end
| _82_523 -> begin
(FStar_All.failwith "todo: translation ml-expr-pure")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x var -> (match (lb) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end
| ((p, guard, expr_r))::tl -> begin
(let _179_294 = (let _179_292 = (translate_expr expr_r var None)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_292))
in (let _179_293 = (translate_match tl fv_x var)
in (translate_pat_guard ((p), (guard)) fv_x _179_294 _179_293)))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_536 fv_x s1 s2 -> (match (_82_536) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_300 = (let _179_299 = (translate_expr_pure v_guard)
in ((_179_299), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_300))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_550) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x)))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_308 = (let _179_307 = (let _179_306 = (let _179_305 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_305)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_306))
in ((_179_307), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_308))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((path, c), lp) -> begin
(

let rec translate_p_ctor = (fun lp fv_x s1 s2 i -> (

let new_fv_x = (match (c) with
| x when (is_prim_constructors x) -> begin
(let _179_325 = (let _179_324 = (let _179_323 = (let _179_322 = (let _179_321 = (let _179_320 = (let _179_319 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_319))
in (Prims.strcat c _179_320))
in (Prims.strcat "Prims._get_" _179_321))
in ((_179_322), (None)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_323))
in ((_179_324), ((fv_x)::[])))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_325))
end
| _82_570 -> begin
(let _179_330 = (let _179_329 = (let _179_328 = (let _179_327 = (let _179_326 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_326))
in ((_179_327), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_328))
in ((fv_x), (_179_329)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_330))
end)
in (match (lp) with
| [] -> begin
s1
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_331 = (translate_p_ctor tl fv_x s1 s2 (i + (Prims.parse_int "1")))
in (translate_pat hd new_fv_x _179_331 s2))
end)))
in (match (c) with
| x when (is_prim_constructors x) -> begin
(

let if_cond = FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat "Prims._is_" c)), (None)))), ((fv_x)::[])))
in (let _179_333 = (let _179_332 = (translate_p_ctor lp fv_x s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_179_332), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_333)))
end
| _82_581 -> begin
(

let isSimple = (match (fv_x) with
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (_82_583) -> begin
true
end
| _82_586 -> begin
false
end)
in if isSimple then begin
(

let if_cond = FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))
in (let _179_335 = (let _179_334 = (translate_p_ctor lp fv_x s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_179_334), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_335)))
end else begin
(

let new_name = (FStar_Absyn_Util.gensym ())
in (

let if_cond = FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))
in (let _179_340 = (let _179_339 = (let _179_338 = (let _179_337 = (let _179_336 = (translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((new_name), (None)))) s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_179_336), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_337))
in (_179_338)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((new_name), (None)))), (Some (fv_x)))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_339)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_340))))
end)
end))
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
(let _179_349 = (translate_p_branch tl fv_x s1 s2)
in (translate_pat hd fv_x s1 _179_349))
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
(let _179_360 = (translate_p_record tl fv_x s1 s2)
in (translate_pat (Prims.snd hd) (new_fv_x (Prims.fst hd)) _179_360 s2))
end)))
in (translate_p_record lp fv_x s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(

let rec translate_p_tuple = (fun lp d fv_x s1 s2 -> (

let new_fv_x = FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int d))), ("")))))))
in (match (lp) with
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_tuple")
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_371 = (translate_p_tuple tl (d + (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat hd new_fv_x _179_371 s2))
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
| FStar_Extraction_ML_Syntax.MLC_Int (s, _82_642) -> begin
(let _179_376 = (let _179_375 = (let _179_374 = (let _179_373 = (FStar_Util.int_of_string s)
in (float_of_int _179_373))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_374))
in ((_179_375), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_376))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_648) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_653) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _82_661) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((id), (None)))), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _179_378 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_378))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_668, t2) -> begin
(let _179_383 = (let _179_382 = (let _179_380 = (let _179_379 = (translate_type t1)
in (((("_1"), (None))), (_179_379)))
in (_179_380)::[])
in (let _179_381 = (translate_type t2)
in ((_179_382), (_179_381), (None))))
in FStar_Extraction_JavaScript_Ast.JST_Function (_179_383))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _179_384 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _179_384)) then begin
(let _179_385 = (FStar_List.map translate_type args)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_385))
end else begin
(

let args_t = (match (args) with
| [] -> begin
None
end
| _82_680 -> begin
(let _179_387 = (FStar_List.map translate_type args)
in (FStar_All.pipe_right _179_387 (fun _179_386 -> Some (_179_386))))
end)
in (let _179_390 = (let _179_389 = (let _179_388 = (getName ((path), (name)))
in FStar_Extraction_JavaScript_Ast.Unqualified (_179_388))
in ((_179_389), (args_t)))
in FStar_Extraction_JavaScript_Ast.JST_Generic (_179_390)))
end
end
end))




