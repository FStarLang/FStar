
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
| FStar_Extraction_ML_Syntax.MLM_Let (_82_87, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_95); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _82_91; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = pt})::[]) -> begin
(

let t = if (not (pt)) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some ([], ty) -> begin
(let _179_81 = (translate_type ty)
in (FStar_All.pipe_right _179_81 (fun _179_80 -> Some (_179_80))))
end
| Some ((_82_109)::_82_107, ty) -> begin
None
end)
end
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in (let _179_88 = (let _179_86 = (let _179_84 = (let _179_83 = (let _179_82 = (translate_expr expr ((name), (None)) None)
in (_179_82)::[])
in (decl_v)::_179_83)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_84))
in (FStar_All.pipe_right _179_86 (fun _179_85 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_85))))
in (FStar_All.pipe_right _179_88 (fun _179_87 -> Some (_179_87))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_82_117) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_120) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_123, name, tparams, body))::[]) -> begin
(

let tparams = None
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (t) -> begin
(let _179_92 = (let _179_91 = (translate_type t)
in ((((name), (None))), (None), (_179_91)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_92))
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Record"), (""))))))::[]
in (

let fields_t = (FStar_List.map (fun _82_140 -> (match (_82_140) with
| (n, t) -> begin
(let _179_94 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" n)), (None)))), (_179_94)))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (None), (FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag fields_t)), ([]), ([]))))))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (lfields) -> begin
(

let tag = (fun n -> (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), (""))))))::[])
in (

let fields_t = (fun fields -> (FStar_List.map (fun t -> (let _179_102 = (let _179_101 = (let _179_100 = (translate_type t)
in (_179_100)::[])
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_101))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_102)))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_151 -> (match (_82_151) with
| (n, l) -> begin
(let _179_108 = (let _179_107 = (let _179_106 = (let _179_105 = (let _179_104 = (fields_t l)
in (FStar_List.append (tag n) _179_104))
in ((_179_105), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_106))
in ((((n), (None))), (None), (_179_107)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_108))
end)) lfields)
in (

let lnames = (FStar_List.map (fun _82_155 -> (match (_82_155) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((n), (None)))), (None)))
end)) lfields)
in (

let union_t = FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (None), (FStar_Extraction_JavaScript_Ast.JST_Union (lnames))))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_List.append lfields_t ((union_t)::[]))))))))
end))
in (

let body_t = (match (body) with
| None -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty] with empty body")
end
| Some (v) -> begin
(forbody v)
end)
in (let _179_112 = (FStar_All.pipe_right body_t (fun _179_110 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_110)))
in (FStar_All.pipe_right _179_112 (fun _179_111 -> Some (_179_111)))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_163) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_166) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_169) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun e var stmt -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let c = (let _179_118 = (let _179_117 = (let _179_116 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_116)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_117))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_118))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_182) -> begin
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
| FStar_Extraction_ML_Syntax.MLE_Let ((_82_198, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_205); FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = pt})::[]), continuation) -> begin
(

let t = if (not (pt)) then begin
None
end else begin
(match (tys) with
| None -> begin
None
end
| Some ([], ty) -> begin
(let _179_120 = (translate_type ty)
in (FStar_All.pipe_right _179_120 (fun _179_119 -> Some (_179_119))))
end
| Some ((_82_221)::_82_219, ty) -> begin
None
end)
end
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (t)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let body_t = (let _179_122 = (let _179_121 = (translate_expr continuation var stmt)
in Some (_179_121))
in (translate_expr body ((name), (None)) _179_122))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(body_t)::[]))))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_230) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args_t = (FStar_List.map translate_expr_app args)
in (

let c = (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_129 = (let _179_128 = (let _179_127 = (let _179_126 = (let _179_125 = (FStar_Util.must (mk_op_bin op))
in (let _179_124 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_123 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_125), (_179_124), (_179_123)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_126))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_127)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_128))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_129))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bool op) -> begin
(let _179_136 = (let _179_135 = (let _179_134 = (let _179_133 = (let _179_132 = (FStar_Util.must (mk_op_bool op))
in (let _179_131 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_130 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_132), (_179_131), (_179_130)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_133))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_134)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_135))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_136))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_un op) -> begin
(let _179_142 = (let _179_141 = (let _179_140 = (let _179_139 = (let _179_138 = (FStar_Util.must (mk_op_un op))
in (let _179_137 = (FStar_List.nth args_t (Prims.parse_int "0"))
in ((_179_138), (_179_137))))
in FStar_Extraction_JavaScript_Ast.JSE_Unary (_179_139))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_140)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_141))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_142))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_82_253, "failwith") -> begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Not yet implemented in ML extraction!")), (""))))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (args_t)))))))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_263) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args_t)))))))
end
| _82_267 -> begin
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
| FStar_Extraction_ML_Syntax.MLE_Record (_82_273, fields) -> begin
(

let c = (let _179_145 = (let _179_144 = (let _179_143 = (translate_expr_app e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_143)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_144))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_145))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_82_282, path) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args_t = (FStar_List.map (fun _82_295 -> (match (_82_295) with
| ((n, _82_292), t) -> begin
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
| FStar_Extraction_ML_Syntax.MLE_CTor (_82_306) -> begin
(

let c = (let _179_149 = (let _179_148 = (let _179_147 = (translate_expr_app e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_147)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_148))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_149))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_82_313) -> begin
(

let c = (let _179_152 = (let _179_151 = (let _179_150 = (translate_expr_app e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_150)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_151))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_152))
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

let c = (let _179_155 = (let _179_154 = (let _179_153 = (translate_expr_app e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_153)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_154))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_155))
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
(let _179_156 = (translate_expr v var None)
in Some (_179_156))
end
| None -> begin
None
end)
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_t), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let c = (let _179_160 = (let _179_159 = (let _179_158 = (let _179_157 = (translate_expr s1 var None)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_t), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (_179_157), (s2_t)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_158))
in Some (_179_159))
in (translate_expr cond ((fv_t), (None)) _179_160))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::(v)::[])
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::[])
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_341) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_344) -> begin
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

let c = (let _179_162 = (let _179_161 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None)))) (FStar_List.length lb) var)
in Some (_179_161))
in (translate_expr e_in ((fv_x), (None)) _179_162))
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
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_366) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_82_370, name) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(

let args_t = (FStar_List.map translate_expr_app args)
in (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_op_bin op) -> begin
(let _179_167 = (let _179_166 = (FStar_Util.must (mk_op_bin op))
in (let _179_165 = (FStar_List.nth args_t (Prims.parse_int "0"))
in (let _179_164 = (FStar_List.nth args_t (Prims.parse_int "1"))
in ((_179_166), (_179_165), (_179_164)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_167))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, function_name) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (args_t)))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_390) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (args_t)))
end
| _82_394 -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let create_fields = (FStar_List.mapi (fun i x -> (let _179_175 = (let _179_174 = (let _179_172 = (let _179_171 = (let _179_170 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_170))
in ((_179_171), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_172))
in (let _179_173 = (translate_expr_app x)
in ((_179_174), (_179_173), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_175))) lexp)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (FStar_List.length lexp)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let create_fields = (FStar_List.map (fun _82_406 -> (match (_82_406) with
| (id, x) -> begin
(let _179_178 = (let _179_177 = (translate_expr_app x)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((((Prims.strcat "_" id)), (None)))), (_179_177), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_178))
end)) fields)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Record")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((p, c), lexpr) -> begin
(let _179_185 = (let _179_184 = (let _179_183 = (let _179_182 = (let _179_181 = (let _179_180 = (let _179_179 = (FStar_List.map translate_expr_app lexpr)
in Some (_179_179))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_180))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_181), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_182))
in (_179_183)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_184)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_185))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (ls) -> begin
(let _179_192 = (let _179_191 = (let _179_190 = (let _179_189 = (let _179_188 = (let _179_187 = (let _179_186 = (FStar_List.map translate_expr_app ls)
in Some (_179_186))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_187))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_188), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_189))
in (_179_190)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Seq")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_191)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_192))
end
| _82_417 -> begin
(FStar_All.failwith "todo: translation of expressions")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  Prims.int  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x d var -> if (d = (Prims.parse_int "0")) then begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end else begin
(

let _82_425 = (FStar_List.nth lb ((FStar_List.length lb) - d))
in (match (_82_425) with
| (p, guard, expr_r) -> begin
(let _179_198 = (translate_expr expr_r var None)
in (let _179_197 = (translate_match lb fv_x (d - (Prims.parse_int "1")) var)
in (translate_pat_guard ((p), (guard)) fv_x _179_198 _179_197)))
end))
end)
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_428 fv_x s1 s2 -> (match (_82_428) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_204 = (let _179_203 = (translate_expr_app v_guard)
in ((_179_203), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_204))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_442) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
s1
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_212 = (let _179_211 = (let _179_210 = (let _179_209 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_209)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_210))
in ((_179_211), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_212))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((p, c), lp) -> begin
(

let if_true = (match ((FStar_List.length lp)) with
| _179_213 when (_179_213 = (Prims.parse_int "0")) -> begin
s1
end
| _179_214 when (_179_214 = (Prims.parse_int "1")) -> begin
(let _179_215 = (FStar_List.nth lp (Prims.parse_int "0"))
in (translate_pat _179_215 (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) s1 s2))
end
| _82_457 -> begin
(translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None))))))) s1 s2)
end)
in FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_StrictEqual), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (c)), (""))))))), (if_true), (Some (s2)))))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_82_460) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_82_463, lp) -> begin
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
(let _179_220 = (translate_p_ctor tl (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "1")))), ("")))))))) s1 s2)
in (translate_pat hd (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) _179_220 s2))
end
| [] -> begin
(FStar_All.failwith "Empty list in pattern matching")
end))
and translate_p_tuple : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp d fv_x s1 s2 -> (

let n = (FStar_List.length lp)
in if (d = (Prims.parse_int "1")) then begin
(let _179_232 = (FStar_List.nth lp (n - d))
in (let _179_231 = (let _179_230 = (let _179_229 = (let _179_228 = (let _179_227 = (let _179_226 = (FStar_Util.string_of_int (n - d))
in (Prims.strcat "_f" _179_226))
in ((_179_227), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_228))
in ((fv_x), (_179_229)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_230))
in (translate_pat _179_232 _179_231 s1 s2)))
end else begin
(let _179_240 = (FStar_List.nth lp (n - d))
in (let _179_239 = (let _179_237 = (let _179_236 = (let _179_235 = (let _179_234 = (let _179_233 = (FStar_Util.string_of_int (n - d))
in (Prims.strcat "_f" _179_233))
in ((_179_234), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_235))
in ((fv_x), (_179_236)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_237))
in (let _179_238 = (translate_p_tuple lp (d - (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat _179_240 _179_239 _179_238 s2))))
end))
and translate_p_record : (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlpattern) Prims.list  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp d fv_x s1 s2 -> (

let n = (FStar_List.length lp)
in if (d = (Prims.parse_int "1")) then begin
(let _179_254 = (let _179_246 = (FStar_List.nth lp (n - d))
in (Prims.snd _179_246))
in (let _179_253 = (let _179_252 = (let _179_251 = (let _179_250 = (let _179_249 = (let _179_248 = (let _179_247 = (FStar_List.nth lp (n - d))
in (Prims.fst _179_247))
in (Prims.strcat "_" _179_248))
in ((_179_249), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_250))
in ((fv_x), (_179_251)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_252))
in (translate_pat _179_254 _179_253 s1 s2)))
end else begin
(let _179_264 = (let _179_255 = (FStar_List.nth lp (n - d))
in (Prims.snd _179_255))
in (let _179_263 = (let _179_261 = (let _179_260 = (let _179_259 = (let _179_258 = (let _179_257 = (let _179_256 = (FStar_List.nth lp (n - d))
in (Prims.fst _179_256))
in (Prims.strcat "_" _179_257))
in ((_179_258), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_259))
in ((fv_x), (_179_260)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_261))
in (let _179_262 = (translate_p_record lp (d - (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat _179_264 _179_263 _179_262 s2))))
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, _82_497) -> begin
(let _179_269 = (let _179_268 = (let _179_267 = (let _179_266 = (FStar_Util.int_of_string s)
in (float_of_int _179_266))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_267))
in ((_179_268), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_269))
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_503) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_508) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
FStar_Extraction_JavaScript_Ast.JST_Any
end
| FStar_Extraction_ML_Syntax.MLTY_Var (id, _82_516) -> begin
FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((id), ("")))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lt) -> begin
(let _179_271 = (FStar_List.map translate_type lt)
in FStar_Extraction_JavaScript_Ast.JST_Tuple (_179_271))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_523, t2) -> begin
(

let t1_t = (translate_type t1)
in (

let t2_t = (translate_type t2)
in FStar_Extraction_JavaScript_Ast.JST_Function (((((((("_1"), (None))), (t1_t)))::[]), (t2_t), (None)))))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, name)) -> begin
(

let args = (FStar_List.mapi (fun i x -> (let _179_278 = (let _179_276 = (let _179_275 = (let _179_274 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_274))
in ((_179_275), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_276))
in (let _179_277 = (translate_type x)
in ((_179_278), (_179_277))))) args)
in (

let tag = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_StringLiteral ((("Tuple"), (""))))))::[]
in (

let arity = (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (None)))), (FStar_Extraction_JavaScript_Ast.JST_NumberLiteral ((((float_of_int (FStar_List.length args))), (""))))))::[]
in if (is_standart_type name) then begin
(FStar_Util.must (mk_standart_type name))
end else begin
if (let _179_279 = (FStar_Extraction_ML_Util.is_xtuple_ty ((path), (name)))
in (FStar_Option.isSome _179_279)) then begin
FStar_Extraction_JavaScript_Ast.JST_Object ((((FStar_List.append tag (FStar_List.append arity args))), ([]), ([])))
end else begin
FStar_Extraction_JavaScript_Ast.JST_Generic (((FStar_Extraction_JavaScript_Ast.Unqualified (((name), (None)))), (None)))
end
end)))
end))




