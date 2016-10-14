
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
Some (FStar_Extraction_JavaScript_Ast.JST_Void)
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


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_50 -> (match (_82_50) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_59 = m
in (match (_82_59) with
| ((prefix, final), _82_56, _82_58) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_69 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _179_74 = (translate_module m)
in Some (_179_74)))
end)
with
| e -> begin
(

let _82_65 = (let _179_76 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_76))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_75 -> (match (_82_75) with
| (module_name, modul, _82_74) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _82_82 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (_82_87, lfunc) -> begin
(

let for1 = (fun _82_101 -> (match (_82_101) with
| {FStar_Extraction_ML_Syntax.mllb_name = (name, _82_99); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _82_95; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let t = if (not (pt)) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some ([], ty) -> begin
(let _179_83 = (translate_type ty)
in (FStar_All.pipe_right _179_83 (fun _179_82 -> Some (_179_82))))
end
| Some ((_82_110)::_82_108, ty) -> begin
None
end)
end
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in (let _179_85 = (let _179_84 = (translate_expr expr ((name), (None)) None)
in (_179_84)::[])
in (decl_v)::_179_85)))
end))
in (let _179_91 = (let _179_89 = (let _179_87 = (FStar_List.collect for1 lfunc)
in (FStar_All.pipe_right _179_87 (fun _179_86 -> FStar_Extraction_JavaScript_Ast.JSS_Block (_179_86))))
in (FStar_All.pipe_right _179_89 (fun _179_88 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_88))))
in (FStar_All.pipe_right _179_91 (fun _179_90 -> Some (_179_90)))))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_118) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_121, name, tparams, body))::[]) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
None
end
| _82_130 -> begin
(let _179_94 = (FStar_List.map (fun _82_134 -> (match (_82_134) with
| (id, _82_133) -> begin
id
end)) tparams)
in (FStar_All.pipe_right _179_94 (fun _179_93 -> Some (_179_93))))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _179_98 = (let _179_97 = (translate_type t)
in ((((name), (None))), (tparams), (_179_97)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_98))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _82_145 -> (match (_82_145) with
| (n, t) -> begin
(let _179_100 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_179_100)))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (tparams), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.map (fun t -> (let _179_108 = (let _179_107 = (let _179_106 = (translate_type t)
in (_179_106)::[])
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_107))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_108)))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_156 -> (match (_82_156) with
| (n, l) -> begin
(let _179_114 = (let _179_113 = (let _179_112 = (let _179_111 = (let _179_110 = (fields_t l)
in (FStar_List.append (tag n) _179_110))
in ((_179_111), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_112))
in ((((n), (None))), (tparams), (_179_113)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_114))
end)) lfields)
in (

let tparams_gen = (match (tparams) with
| Some (t) -> begin
(let _179_117 = (FStar_List.map (fun x -> FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((x), (None)))), (None)))) t)
in (FStar_All.pipe_right _179_117 (fun _179_116 -> Some (_179_116))))
end
| None -> begin
None
end)
in (

let lnames = (FStar_List.map (fun _82_165 -> (match (_82_165) with
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
in (let _179_121 = (FStar_All.pipe_right body_t (fun _179_119 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_119)))
in (FStar_All.pipe_right _179_121 (fun _179_120 -> Some (_179_120)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_173) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_176) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_179) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun e var stmt -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let c = (let _179_127 = (let _179_126 = (let _179_125 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_125)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_126))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_127))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_192) -> begin
(

let c = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))))))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
(

let c = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((n), (None)))))))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((_82_208, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_215); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let t = if (not (pt)) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some ([], ty) -> begin
(let _179_129 = (translate_type ty)
in (FStar_All.pipe_right _179_129 (fun _179_128 -> Some (_179_128))))
end
| Some ((_82_231)::_82_229, ty) -> begin
None
end)
end
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let body_t = (let _179_131 = (let _179_130 = (translate_expr continuation var stmt)
in Some (_179_130))
in (translate_expr body ((name), (None)) _179_131))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(body_t)::[]))))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_240) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args_t = (FStar_List.map translate_expr_app args)
in (

let c = (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_138 = (let _179_137 = (let _179_136 = (let _179_135 = (let _179_134 = (FStar_Util.must (mk_op_bin op))
in (let _179_133 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_132 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_134), (_179_133), (_179_132)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_135))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_136)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_137))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_138))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_145 = (let _179_144 = (let _179_143 = (let _179_142 = (let _179_141 = (FStar_Util.must (mk_op_bool op))
in (let _179_140 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_139 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_141), (_179_140), (_179_139)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_142))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_143)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_144))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_145))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_151 = (let _179_150 = (let _179_149 = (let _179_148 = (let _179_147 = (FStar_Util.must (mk_op_un op))
in (let _179_146 = (FStar_List.nth args_t (Prims.parse_int "0"))
in ((_179_147), (_179_146))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_148))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_149)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_150))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_151))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_82_263, "failwith") -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Not yet implemented in ML extraction!")), (""))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (args_t)))))))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_273) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args_t)))))))
end
| _82_277 -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end)
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_283, fields) -> begin
(

let c = (let _179_154 = (let _179_153 = (let _179_152 = (translate_expr_app e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_152)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_153))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_154))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_82_292, path) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args_t = (FStar_List.map (fun _82_305 -> (match (_82_305) with
| ((n, _82_302), t) -> begin
FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (None)))
end)) args)
in (

let fv = (FStar_Absyn_Util.gensym ())
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let body_t = (translate_expr body ((fv), (None)) (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv), (None))))))))
in (

let fun_t = FStar_Extraction_JavaScript_Ast.JSE_Function (((None), (args_t), (FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((decl_v)::(body_t)::[])), (None), (None)))
in (

let c = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (fun_t))))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_82_316) -> begin
(

let c = (let _179_158 = (let _179_157 = (let _179_156 = (translate_expr_app e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_156)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_157))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_158))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_82_323) -> begin
(

let c = (let _179_161 = (let _179_160 = (let _179_159 = (translate_expr_app e)
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
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(

let c = (let _179_164 = (let _179_163 = (let _179_162 = (translate_expr_app e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_162)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_163))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_164))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let fv_t = (FStar_Absyn_Util.gensym ())
in (

let s2_t = (match (s2) with
| Some (v) -> begin
(let _179_165 = (translate_expr v var None)
in Some (_179_165))
end
| None -> begin
None
end)
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_t), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let c = (let _179_169 = (let _179_168 = (let _179_167 = (let _179_166 = (translate_expr s1 var None)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_t), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (_179_166), (s2_t)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_167))
in Some (_179_168))
in (translate_expr cond ((fv_t), (None)) _179_169))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::(v)::[])
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::[])
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_351) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_354) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(translate_expr in_e var stmt)
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let fv_x = "_x"
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let c = (let _179_171 = (let _179_170 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None)))) (FStar_List.length lb) var)
in Some (_179_170))
in (translate_expr e_in ((fv_x), (None)) _179_171))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::(v)::[])
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::[])
end))))
end))
and translate_expr_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_376) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_82_380, name) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args_t = (FStar_List.map translate_expr_app args)
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_176 = (let _179_175 = (FStar_Util.must (mk_op_bin op))
in (let _179_174 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_173 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_175), (_179_174), (_179_173)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_176))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_180 = (let _179_179 = (FStar_Util.must (mk_op_bool op))
in (let _179_178 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_177 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_179), (_179_178), (_179_177)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_180))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_183 = (let _179_182 = (FStar_Util.must (mk_op_un op))
in (let _179_181 = (FStar_List.nth args_t (Prims.parse_int "0"))
in ((_179_182), (_179_181))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_183))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (args_t)))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_410) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args_t)))
end
| _82_414 -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let create_fields = (FStar_List.mapi (fun i x -> (let _179_191 = (let _179_190 = (let _179_188 = (let _179_187 = (let _179_186 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_186))
in ((_179_187), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_188))
in (let _179_189 = (translate_expr_app x)
in ((_179_190), (_179_189), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_191))) lexp)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (FStar_List.length lexp)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _82_426 -> (match (_82_426) with
| (id, x) -> begin
(let _179_194 = (let _179_193 = (translate_expr_app x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_193), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_194))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((p, c), lexpr) -> begin
(let _179_201 = (let _179_200 = (let _179_199 = (let _179_198 = (let _179_197 = (let _179_196 = (let _179_195 = (FStar_List.map translate_expr_app lexpr)
in Some (_179_195))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_196))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_197), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_198))
in (_179_199)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_200)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_201))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(let _179_208 = (let _179_207 = (let _179_206 = (let _179_205 = (let _179_204 = (let _179_203 = (let _179_202 = (FStar_List.map translate_expr_app ls)
in Some (_179_202))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_203))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_204), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_205))
in (_179_206)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Seq")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_207)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_208))
end
| _82_437 -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("TODO!!!")), ("")))
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  Prims.int  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x d var -> if (d = (Prims.parse_int "0")) then begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end else begin
(

let _82_445 = (FStar_List.nth lb ((FStar_List.length lb) - d))
in (match (_82_445) with
| (p, guard, expr_r) -> begin
(let _179_214 = (translate_expr expr_r var None)
in (let _179_213 = (translate_match lb fv_x (d - (Prims.parse_int "1")) var)
in (translate_pat_guard ((p), (guard)) fv_x _179_214 _179_213)))
end))
end)
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_448 fv_x s1 s2 -> (match (_82_448) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_220 = (let _179_219 = (translate_expr_app v_guard)
in ((_179_219), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_220))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_462) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_228 = (let _179_227 = (let _179_226 = (let _179_225 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_225)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_226))
in ((_179_227), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_228))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((p, c), lp) -> begin
(

let if_true = (match ((FStar_List.length lp)) with
| _179_229 when (_179_229 = (Prims.parse_int "0")) -> begin
s1
end
| _179_230 when (_179_230 = (Prims.parse_int "1")) -> begin
(let _179_231 = (FStar_List.nth lp (Prims.parse_int "0"))
in (translate_pat _179_231 (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) s1 s2))
end
| _82_477 -> begin
(translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None))))))) s1 s2)
end)
in FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))), (if_true), (Some (s2)))))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_82_480) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_82_483, lp) -> begin
(translate_p_record lp (FStar_List.length lp) fv_x s1 s2)
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(translate_p_tuple lp (FStar_List.length lp) fv_x s1 s2)
end))
and translate_p_ctor : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(translate_pat x fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_236 = (translate_p_ctor tl (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "1")))), ("")))))))) s1 s2)
in (translate_pat hd (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) _179_236 s2))
end
| [] -> begin
(FStar_All.failwith "Empty list in pattern matching")
end))
and translate_p_tuple : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp d fv_x s1 s2 -> (

let n = (FStar_List.length lp)
in if (d = (Prims.parse_int "1")) then begin
(let _179_248 = (FStar_List.nth lp (n - d))
in (let _179_247 = (let _179_246 = (let _179_245 = (let _179_244 = (let _179_243 = (let _179_242 = (FStar_Util.string_of_int (n - d))
in (Prims.strcat "_f" _179_242))
in ((_179_243), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_244))
in ((fv_x), (_179_245)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_246))
in (translate_pat _179_248 _179_247 s1 s2)))
end else begin
(let _179_256 = (FStar_List.nth lp (n - d))
in (let _179_255 = (let _179_253 = (let _179_252 = (let _179_251 = (let _179_250 = (let _179_249 = (FStar_Util.string_of_int (n - d))
in (Prims.strcat "_f" _179_249))
in ((_179_250), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_251))
in ((fv_x), (_179_252)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_253))
in (let _179_254 = (translate_p_tuple lp (d - (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat _179_256 _179_255 _179_254 s2))))
end))
and translate_p_record : (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlpattern) Prims.list  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp d fv_x s1 s2 -> (

let n = (FStar_List.length lp)
in if (d = (Prims.parse_int "1")) then begin
(let _179_270 = (let _179_262 = (FStar_List.nth lp (n - d))
in (Prims.snd _179_262))
in (let _179_269 = (let _179_268 = (let _179_267 = (let _179_266 = (let _179_265 = (let _179_264 = (let _179_263 = (FStar_List.nth lp (n - d))
in (Prims.fst _179_263))
in (Prims.strcat "_" _179_264))
in ((_179_265), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_266))
in ((fv_x), (_179_267)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_268))
in (translate_pat _179_270 _179_269 s1 s2)))
end else begin
(let _179_280 = (let _179_271 = (FStar_List.nth lp (n - d))
in (Prims.snd _179_271))
in (let _179_279 = (let _179_277 = (let _179_276 = (let _179_275 = (let _179_274 = (let _179_273 = (let _179_272 = (FStar_List.nth lp (n - d))
in (Prims.fst _179_272))
in (Prims.strcat "_" _179_273))
in ((_179_274), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_275))
in ((fv_x), (_179_276)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_277))
in (let _179_278 = (translate_p_record lp (d - (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat _179_280 _179_279 _179_278 s2))))
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, _82_517) -> begin
(let _179_285 = (let _179_284 = (let _179_283 = (let _179_282 = (FStar_Util.int_of_string s)
in (float_of_int _179_282))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_283))
in ((_179_284), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_285))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_523) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_528) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _82_536) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((id), (None)))), (None)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _179_287 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_287))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_543, t2) -> begin
(

let t1_t = (translate_type t1)
in (

let t2_t = (translate_type t2)
in FStar_Extraction_JavaScript_Ast.JST_Any))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _179_288 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _179_288)) then begin
(

let args = (FStar_List.mapi (fun i x -> (let _179_295 = (let _179_293 = (let _179_292 = (let _179_291 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_291))
in ((_179_292), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_293))
in (let _179_294 = (translate_type x)
in ((_179_295), (_179_294))))) args)
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
| _82_562 -> begin
(let _179_297 = (FStar_List.map translate_type args)
in (FStar_All.pipe_right _179_297 (fun _179_296 -> Some (_179_296))))
end)
in (

let name = (match (name) with
| ("list") | ("option") -> begin
(FStar_Extraction_ML_Syntax.string_of_mlpath ((path), (name)))
end
| _82_567 -> begin
name
end)
in FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((name), (None)))), (args)))))
end
end
end))




