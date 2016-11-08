
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


let rec get_Generic : FStar_Extraction_JavaScript_Ast.typ  ->  Prims.string Prims.list = (fun t -> (match (t) with
| FStar_Extraction_JavaScript_Ast.JST_Generic (g, v) -> begin
(match (v) with
| Some (v1) -> begin
(FStar_List.collect get_Generic v1)
end
| None -> begin
(match (g) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _82_111) -> begin
if ((FStar_String.get id (Prims.parse_int "0")) = '\'') then begin
(id)::[]
end else begin
[]
end
end
| _82_115 -> begin
[]
end)
end)
end
| FStar_Extraction_JavaScript_Ast.JST_Function (_82_117, _82_119, gen_d) -> begin
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
| FStar_Extraction_JavaScript_Ast.JST_Object (l, _82_130, _82_132) -> begin
(FStar_List.collect (fun _82_138 -> (match (_82_138) with
| (_82_136, t) -> begin
(get_Generic t)
end)) l)
end
| _82_140 -> begin
[]
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_142 -> (match (_82_142) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_151 = m
in (match (_82_151) with
| ((prefix, final), _82_148, _82_150) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_161 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (

let _82_163 = (FStar_ST.op_Colon_Equals export_modules [])
in (let _179_85 = (translate_module m)
in Some (_179_85))))
end)
with
| e -> begin
(

let _82_157 = (let _179_87 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_87))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_169 -> (match (_82_169) with
| (module_name, modul, _82_168) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(

let _82_175 = (FStar_ST.op_Colon_Equals current_module_name (FStar_String.concat "_" module_name))
in (

let res = (FStar_List.filter_map translate_decl decls)
in (

let create_module_imports = (let _179_94 = (let _179_92 = (let _179_90 = (FStar_ST.read export_modules)
in (FStar_List.map (fun m -> FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (((m), (None)))) _179_90))
in (FStar_All.pipe_right _179_92 (fun _179_91 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_91))))
in (FStar_All.pipe_right _179_94 (fun _179_93 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_93))))
in (FStar_List.append ((create_module_imports)::[]) res))))
end
| _82_181 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (_82_185, c_flag, lfunc) -> begin
(

let for1 = (fun _82_199 -> (match (_82_199) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, _82_197); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = if (not (pt)) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some ([], ty) -> begin
(let _179_99 = (translate_type ty)
in (FStar_All.pipe_right _179_99 (fun _179_98 -> Some (_179_98))))
end
| Some (lp, ty) -> begin
(match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_211, t2) -> begin
(

let lp = (match (lp) with
| [] -> begin
None
end
| _82_217 -> begin
(let _179_102 = (FStar_List.map (fun _82_221 -> (match (_82_221) with
| (id, _82_220) -> begin
id
end)) lp)
in (FStar_All.pipe_right _179_102 (fun _179_101 -> Some (_179_101))))
end)
in if unit_b then begin
None
end else begin
(let _179_109 = (let _179_107 = (let _179_106 = (let _179_104 = (let _179_103 = (translate_type t1)
in (((("_1"), (None))), (_179_103)))
in (_179_104)::[])
in (let _179_105 = (translate_type t2)
in ((_179_106), (_179_105), (lp))))
in FStar_Extraction_JavaScript_Ast.JST_Function (_179_107))
in (FStar_All.pipe_right _179_109 (fun _179_108 -> Some (_179_108))))
end)
end
| _82_224 -> begin
None
end)
end)
end
in (

let is_private = (FStar_List.contains FStar_Extraction_ML_Syntax.Private c_flag)
in if (is_pure_expr expr ((name), (None))) then begin
(

let c = (let _179_113 = (let _179_112 = (let _179_111 = (let _179_110 = (translate_expr_pure expr)
in Some (_179_110))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (_179_111)))
in ((_179_112), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_113))
in if is_private then begin
(c)::[]
end else begin
(FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (c)), (FStar_Extraction_JavaScript_Ast.ExportValue))))::[]
end)
end else begin
(

let c = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let c1 = (translate_expr expr ((name), (t)) None)
in if is_private then begin
(c)::(c1)::[]
end else begin
(FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (((FStar_Extraction_JavaScript_Ast.JSE_Declaration (c)), (FStar_Extraction_JavaScript_Ast.ExportValue))))::(c1)::[]
end))
end))
end))
in (let _179_119 = (let _179_117 = (let _179_115 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _179_115 (fun _179_114 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_114))))
in (FStar_All.pipe_right _179_117 (fun _179_116 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_116))))
in (FStar_All.pipe_right _179_119 (fun _179_118 -> Some (_179_118)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_231) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_234, name, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| _82_243 -> begin
(let _179_122 = (FStar_List.map (fun _82_247 -> (match (_82_247) with
| (id, _82_246) -> begin
id
end)) tparams)
in (FStar_All.pipe_right _179_122 (fun _179_121 -> Some (_179_121))))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _179_126 = (let _179_125 = (translate_type t)
in ((((name), (None))), (tparams), (_179_125)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_126))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _82_258 -> (match (_82_258) with
| (n, t) -> begin
(let _179_128 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_179_128)))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.mapi (fun i t -> (let _179_139 = (let _179_137 = (let _179_136 = (let _179_135 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_135))
in ((_179_136), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_137))
in (let _179_138 = (translate_type t)
in ((_179_139), (_179_138))))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_270 -> (match (_82_270) with
| (n, l) -> begin
(let _179_145 = (let _179_144 = (let _179_143 = (let _179_142 = (let _179_141 = (fields_t l)
in (FStar_List.append (tag n) _179_141))
in ((_179_142), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_143))
in ((((n), (None))), (tparams), (_179_144)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_145))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _179_148 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((x), (None)))), (None)))) t)
in (FStar_All.pipe_right _179_148 (fun _179_147 -> Some (_179_147))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun _82_279 -> (match (_82_279) with
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
in (let _179_152 = (FStar_All.pipe_right body_t (fun _179_150 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_150)))
in (FStar_All.pipe_right _179_152 (fun _179_151 -> Some (_179_151)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_287) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_290) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _179_155 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block ([])) (fun _179_153 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_153)))
in (FStar_All.pipe_right _179_155 (fun _179_154 -> Some (_179_154))))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_297) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun e var stmt -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| x when (is_pure_expr e var) -> begin
(

let c = (let _179_161 = (let _179_160 = (let _179_159 = (translate_expr_pure e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_159)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_160))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_161))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((_82_308, _82_310, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_317); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
if (is_pure_expr body ((name), (None))) then begin
(let _179_170 = (let _179_168 = (let _179_165 = (let _179_164 = (let _179_163 = (let _179_162 = (translate_expr_pure body)
in Some (_179_162))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (_179_163)))
in ((_179_164), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_165))
in (let _179_167 = (let _179_166 = (translate_expr continuation var stmt)
in (_179_166)::[])
in (_179_168)::_179_167))
in (FStar_All.pipe_right _179_170 (fun _179_169 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_169))))
end else begin
(let _179_172 = (let _179_171 = (translate_expr continuation var stmt)
in Some (_179_171))
in (translate_expr body ((name), (None)) _179_172))
end
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_326) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let generic_t = (FStar_ST.alloc [])
in (

let addUnique = (fun lst -> (FStar_List.map (fun el -> if (not ((let _179_177 = (FStar_ST.read generic_t)
in (FStar_List.existsb (fun x -> (x = el)) _179_177)))) then begin
(let _179_179 = (let _179_178 = (FStar_ST.read generic_t)
in (FStar_List.append ((el)::[]) _179_178))
in (FStar_ST.op_Colon_Equals generic_t _179_179))
end else begin
()
end) lst))
in (

let args = (FStar_List.map (fun _82_342 -> (match (_82_342) with
| ((n, _82_339), t) -> begin
(

let t = (translate_type t)
in (

let _82_344 = (let _179_182 = (let _179_181 = (get_Generic t)
in (addUnique _179_181))
in (FStar_All.pipe_right _179_182 Prims.ignore))
in FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (Some (t))))))
end)) args)
in (

let generic_r = (match ((FStar_ST.read generic_t)) with
| [] -> begin
None
end
| _82_349 -> begin
(let _179_183 = (FStar_ST.read generic_t)
in Some (_179_183))
end)
in (

let body_t = if (is_pure_expr body var) then begin
(let _179_184 = (translate_expr_pure body)
in FStar_Extraction_JavaScript_Ast.JS_BodyExpression (_179_184))
end else begin
(let _179_187 = (let _179_186 = (let _179_185 = (translate_expr body (("_res"), (None)) (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_res"), (None))))))))
in (_179_185)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_res"), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_186)
in FStar_Extraction_JavaScript_Ast.JS_BodyBlock (_179_187))
end
in (

let ret_t = (match ((Prims.snd var)) with
| None -> begin
None
end
| Some (v) -> begin
(match (v) with
| FStar_Extraction_JavaScript_Ast.JST_Function (_82_356, t2, _82_359) -> begin
Some (t2)
end
| _82_363 -> begin
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
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let s2 = (match (s2) with
| Some (v) -> begin
(let _179_188 = (translate_expr v var None)
in Some (_179_188))
end
| None -> begin
None
end)
in (

let c = if (is_pure_expr cond var) then begin
(let _179_191 = (let _179_190 = (translate_expr_pure cond)
in (let _179_189 = (translate_expr s1 var None)
in ((_179_190), (_179_189), (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_191))
end else begin
(let _179_199 = (let _179_197 = (let _179_196 = (let _179_195 = (let _179_194 = (let _179_193 = (let _179_192 = (translate_expr s1 var None)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (_179_192), (s2)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_193))
in Some (_179_194))
in (translate_expr cond (("_cond"), (None)) _179_195))
in (_179_196)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_cond"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_197)
in (FStar_All.pipe_right _179_199 (fun _179_198 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_198))))
end
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_383) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_386) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(

let var = (let _179_201 = (let _179_200 = (translate_type in_e.FStar_Extraction_ML_Syntax.mlty)
in Some (_179_200))
in (((Prims.fst var)), (_179_201)))
in (translate_expr in_e var stmt))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let c = if (is_pure_expr e_in var) then begin
(let _179_202 = (translate_expr_pure e_in)
in (translate_match lb _179_202 var))
end else begin
(let _179_208 = (let _179_206 = (let _179_205 = (let _179_204 = (let _179_203 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_match_e"), (None)))) var)
in Some (_179_203))
in (translate_expr e_in (("_match_e"), (None)) _179_204))
in (_179_205)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_match_e"), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_206)
in (FStar_All.pipe_right _179_208 (fun _179_207 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_207))))
end
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
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
(let _179_212 = (let _179_211 = (translate_seq tl)
in Some (_179_211))
in (translate_expr hd (("_"), (None)) _179_212))
end))
in (

let c = (translate_seq ls)
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
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

let stmt = (match (stmt) with
| Some (v) -> begin
(v)::[]
end
| None -> begin
[]
end)
in (

let expr = if ((Prims.fst var) = "_res") then begin
(let _179_217 = (let _179_216 = (let _179_215 = (let _179_214 = (let _179_213 = (translate_arg_app e args var)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_213)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_214))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_215))
in (_179_216)::[])
in (FStar_List.append _179_217 stmt))
end else begin
(let _179_225 = (let _179_224 = (let _179_223 = (let _179_222 = (let _179_221 = (let _179_220 = (let _179_219 = (let _179_218 = (translate_arg_app e args var)
in Some (_179_218))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_219)))
in ((_179_220), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_221))
in (_179_222)::[])
in (FStar_List.append _179_223 stmt))
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_224))
in (_179_225)::[])
end
in (let _179_227 = (let _179_226 = (FStar_ST.read new_fv)
in (FStar_List.append _179_226 expr))
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_227))))))
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
| _82_437 -> begin
(let _179_236 = (let _179_235 = (FStar_List.mapi (fun i x -> (let _179_234 = (let _179_233 = (let _179_232 = (let _179_231 = (let _179_230 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_230))
in ((_179_231), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_232))
in ((_179_233), (x), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_234))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _179_235))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_236))
end)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (expr))))
in (

let stmt = (match (stmt) with
| Some (v) -> begin
(v)::[]
end
| None -> begin
[]
end)
in (let _179_238 = (let _179_237 = (FStar_ST.read new_fv)
in (FStar_List.append _179_237 ((FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append ((expr)::[]) stmt)))::[])))
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_238)))))))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.map (fun _82_453 -> (match (_82_453) with
| (id, x) -> begin
(let _179_242 = (let _179_241 = (let _179_240 = (create_pure_args new_fv ((x)::[]) var)
in (FStar_List.nth _179_240 (Prims.parse_int "0")))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_241), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_242))
end)) fields)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))))))
in (

let stmt = (match (stmt) with
| Some (v) -> begin
(v)::[]
end
| None -> begin
[]
end)
in (let _179_244 = (let _179_243 = (FStar_ST.read new_fv)
in (FStar_List.append _179_243 ((FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append ((expr)::[]) stmt)))::[])))
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_244))))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let new_fv = (FStar_ST.alloc [])
in (

let create_fields = (FStar_List.mapi (fun i x -> (let _179_253 = (let _179_252 = (let _179_249 = (let _179_248 = (let _179_247 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_247))
in ((_179_248), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_249))
in (let _179_251 = (let _179_250 = (create_pure_args new_fv ((x)::[]) var)
in (FStar_List.nth _179_250 (Prims.parse_int "0")))
in ((_179_252), (_179_251), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_253))) lexp)
in (

let expr = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (FStar_List.length lexp)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields))))))
in (

let stmt = (match (stmt) with
| Some (v) -> begin
(v)::[]
end
| None -> begin
[]
end)
in (let _179_255 = (let _179_254 = (FStar_ST.read new_fv)
in (FStar_List.append _179_254 ((FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append ((expr)::[]) stmt)))::[])))
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_255))))))
end
| _82_472 -> begin
(FStar_All.failwith "todo: translation ml-expr")
end))
and create_pure_args : FStar_Extraction_JavaScript_Ast.statement_t Prims.list FStar_ST.ref  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list = (fun new_fv args var -> (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _82_481) when ((c = "Nil") || (c = "None")) -> begin
(let _179_262 = (let _179_261 = (translate_expr_pure x)
in (let _179_260 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_261), (_179_260))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_262))
end
| _82_485 -> begin
if (is_pure_expr x var) then begin
(translate_expr_pure x)
end else begin
(

let fv_x = (FStar_Absyn_Util.gensym ())
in (

let c = (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (_82_488) -> begin
(let _179_267 = (let _179_266 = (let _179_265 = (let _179_264 = (let _179_263 = (translate_expr_pure x)
in Some (_179_263))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (_179_264)))
in ((_179_265), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_266))
in (_179_267)::[])
end
| _82_491 -> begin
(let _179_269 = (let _179_268 = (translate_expr x ((fv_x), (None)) None)
in (_179_268)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (None))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::_179_269)
end)
in (

let _82_493 = (let _179_271 = (let _179_270 = (FStar_ST.read new_fv)
in (FStar_List.append _179_270 c))
in (FStar_ST.op_Colon_Equals new_fv _179_271))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None))))))
end
end)) args))
and translate_arg_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e args var -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_278 = (let _179_277 = (FStar_Util.must (mk_op_bin op))
in (let _179_276 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_275 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_277), (_179_276), (_179_275)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_278))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_282 = (let _179_281 = (FStar_Util.must (mk_op_bool op))
in (let _179_280 = (FStar_List.nth args (Prims.parse_int "0"))
in (let _179_279 = (FStar_List.nth args (Prims.parse_int "1"))
in ((_179_281), (_179_280), (_179_279)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_282))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_286 = (let _179_285 = (let _179_283 = (mk_op_un op)
in (FStar_Util.must _179_283))
in (let _179_284 = (FStar_List.nth args (Prims.parse_int "0"))
in ((_179_285), (_179_284))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_286))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
(let _179_289 = (let _179_288 = (let _179_287 = (getName ((path), (function_name)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_287))
in ((_179_288), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_289))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_519) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args)))
end
| _82_523 -> begin
if (is_pure_expr e var) then begin
(let _179_291 = (let _179_290 = (translate_expr_pure e)
in ((_179_290), (args)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_291))
end else begin
(FStar_All.failwith "todo: translation [MLE_App]")
end
end))
and translate_expr_pure : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_529) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
(let _179_293 = (getName ((path), (n)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_293))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let create_fields = (FStar_List.mapi (fun i x -> (let _179_301 = (let _179_300 = (let _179_298 = (let _179_297 = (let _179_296 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_296))
in ((_179_297), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_298))
in (let _179_299 = (translate_expr_pure x)
in ((_179_300), (_179_299), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_301))) lexp)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (FStar_List.length lexp)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _82_547 -> (match (_82_547) with
| (id, x) -> begin
(let _179_304 = (let _179_303 = (translate_expr_pure x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_303), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_304))
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
(let _179_312 = (let _179_311 = (let _179_309 = (let _179_308 = (let _179_307 = (let _179_306 = (let _179_305 = (translate_expr_pure hd)
in (_179_305)::[])
in Some (_179_306))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_307))
in ((_179_308), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("concat"), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_309))
in (let _179_310 = (FStar_List.map translate_expr_pure tl)
in ((_179_311), (_179_310))))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_312))
end)
end
| x when (is_prim_constructors x) -> begin
(let _179_314 = (let _179_313 = (FStar_List.map translate_expr_pure lexpr)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat "Prims._mk_" c)), (None)))), (_179_313)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_314))
end
| _82_562 -> begin
(let _179_324 = (let _179_323 = (FStar_List.mapi (fun i x -> (let _179_322 = (let _179_321 = (let _179_319 = (let _179_318 = (let _179_317 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_317))
in ((_179_318), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_319))
in (let _179_320 = (translate_expr_pure x)
in ((_179_321), (_179_320), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_322))) lexpr)
in (FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) _179_323))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_324))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _82_567, _82_569) -> begin
(translate_expr_pure e)
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args = (FStar_List.map (fun x -> (match (x.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((path, c), _82_581) when ((c = "Nil") || (c = "None")) -> begin
(let _179_328 = (let _179_327 = (translate_expr_pure x)
in (let _179_326 = (translate_type x.FStar_Extraction_ML_Syntax.mlty)
in ((_179_327), (_179_326))))
in FStar_Extraction_JavaScript_Ast.JSE_TypeCast (_179_328))
end
| _82_585 -> begin
(translate_expr_pure x)
end)) args)
in (translate_arg_app e args ((""), (None))))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (expr, (path, name)) -> begin
(let _179_330 = (let _179_329 = (translate_expr_pure expr)
in ((_179_329), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((((Prims.strcat "_" name)), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_330))
end
| _82_594 -> begin
(FStar_All.failwith "todo: translation ml-expr-pure")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x var -> (match (lb) with
| [] -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end
| ((p, guard, expr_r))::tl -> begin
(let _179_335 = (translate_expr expr_r var None)
in (let _179_334 = (translate_match tl fv_x var)
in (translate_pat_guard ((p), (guard)) fv_x _179_335 _179_334)))
end))
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_607 fv_x s1 s2 -> (match (_82_607) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_341 = (let _179_340 = (translate_expr_pure v_guard)
in ((_179_340), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_341))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_621) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x)))), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_349 = (let _179_348 = (let _179_347 = (let _179_346 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_346)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_347))
in ((_179_348), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_349))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((path, c), lp) -> begin
(

let rec translate_p_ctor = (fun lp fv_x s1 s2 i -> (

let new_fv_x = (match (c) with
| x when (is_prim_constructors x) -> begin
(let _179_366 = (let _179_365 = (let _179_364 = (let _179_363 = (let _179_362 = (let _179_361 = (let _179_360 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_360))
in (Prims.strcat c _179_361))
in (Prims.strcat "Prims._get_" _179_362))
in ((_179_363), (None)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_364))
in ((_179_365), ((fv_x)::[])))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_366))
end
| _82_641 -> begin
(let _179_371 = (let _179_370 = (let _179_369 = (let _179_368 = (let _179_367 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_367))
in ((_179_368), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_369))
in ((fv_x), (_179_370)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_371))
end)
in (match (lp) with
| [] -> begin
s1
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_372 = (translate_p_ctor tl fv_x s1 s2 (i + (Prims.parse_int "1")))
in (translate_pat hd new_fv_x _179_372 s2))
end)))
in (

let if_cond = (match (c) with
| x when (is_prim_constructors x) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((((Prims.strcat "Prims._is_" c)), (None)))), ((fv_x)::[])))
end
| _82_651 -> begin
FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))
end)
in (let _179_374 = (let _179_373 = (translate_p_ctor lp fv_x s1 s2 (Prims.parse_int "0"))
in ((if_cond), (_179_373), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_374))))
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
(let _179_383 = (translate_p_branch tl fv_x s1 s2)
in (translate_pat hd fv_x s1 _179_383))
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
(let _179_394 = (translate_p_record tl fv_x s1 s2)
in (translate_pat (Prims.snd hd) (new_fv_x (Prims.fst hd)) _179_394 s2))
end)))
in (translate_p_record lp fv_x s1 s2))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(

let rec translate_p_tuple = (fun lp d fv_x s1 s2 -> (

let new_fv_x = (let _179_409 = (let _179_408 = (let _179_407 = (let _179_406 = (let _179_405 = (FStar_Util.string_of_int d)
in (Prims.strcat "_" _179_405))
in ((_179_406), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_407))
in ((fv_x), (_179_408)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_409))
in (match (lp) with
| [] -> begin
(FStar_All.failwith "Empty list in translate_p_tuple")
end
| (x)::[] -> begin
(translate_pat x new_fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_410 = (translate_p_tuple tl (d + (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat hd new_fv_x _179_410 s2))
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
| FStar_Extraction_ML_Syntax.MLC_Int (s, _82_704) -> begin
(let _179_415 = (let _179_414 = (let _179_413 = (let _179_412 = (FStar_Util.int_of_string s)
in (float_of_int _179_412))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_413))
in ((_179_414), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_415))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_710) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_715) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _82_723) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((id), (None)))), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _179_417 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_417))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_730, t2) -> begin
(

let t1_t = (translate_type t1)
in (

let t2_t = (translate_type t2)
in (

let generic_t = (FStar_ST.alloc [])
in (

let addUnique = (fun lst -> (FStar_List.map (fun el -> if (not ((let _179_422 = (FStar_ST.read generic_t)
in (FStar_List.existsb (fun x -> (x = el)) _179_422)))) then begin
(let _179_424 = (let _179_423 = (FStar_ST.read generic_t)
in (FStar_List.append ((el)::[]) _179_423))
in (FStar_ST.op_Colon_Equals generic_t _179_424))
end else begin
()
end) lst))
in (

let _82_741 = (let _179_426 = (let _179_425 = (get_Generic t1_t)
in (addUnique _179_425))
in (FStar_All.pipe_right _179_426 Prims.ignore))
in (

let _82_743 = (let _179_428 = (let _179_427 = (get_Generic t2_t)
in (addUnique _179_427))
in (FStar_All.pipe_right _179_428 Prims.ignore))
in (

let generic_r = (match ((FStar_ST.read generic_t)) with
| [] -> begin
None
end
| _82_747 -> begin
(let _179_429 = (FStar_ST.read generic_t)
in Some (_179_429))
end)
in FStar_Extraction_JavaScript_Ast.JST_Function (((((((("_1"), (None))), (t1_t)))::[]), (t2_t), (generic_r))))))))))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _179_430 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _179_430)) then begin
(

let args = (FStar_List.mapi (fun i x -> (let _179_437 = (let _179_435 = (let _179_434 = (let _179_433 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_433))
in ((_179_434), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_435))
in (let _179_436 = (translate_type x)
in ((_179_437), (_179_436))))) args)
in (

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Tuple"), (""))))))::[]
in (

let arity = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_NumberLiteral ((((float_of_int (FStar_List.length args))), (""))))))::[]
in FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag (FStar_List.append arity args))), ([]), ([]))))))
end else begin
(

let args_t = (match (args) with
| [] -> begin
None
end
| _82_762 -> begin
(let _179_439 = (FStar_List.map translate_type args)
in (FStar_All.pipe_right _179_439 (fun _179_438 -> Some (_179_438))))
end)
in (let _179_442 = (let _179_441 = (let _179_440 = (getName ((path), (name)))
in FStar_Extraction_JavaScript_Ast.Unqualified (_179_440))
in ((_179_441), (args_t)))
in FStar_Extraction_JavaScript_Ast.JST_Generic (_179_442)))
end
end
end))




