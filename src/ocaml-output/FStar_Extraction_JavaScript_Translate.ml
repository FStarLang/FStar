
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
| _82_24 -> begin
None
end))


let is_op_bin : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bin op) <> None))


let mk_op_bool : Prims.string  ->  FStar_Extraction_JavaScript_Ast.op_log Prims.option = (fun _82_2 -> (match (_82_2) with
| "op_AmpAmp" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_And)
end
| "op_BarBar" -> begin
Some (FStar_Extraction_JavaScript_Ast.JSL_Or)
end
| _82_30 -> begin
None
end))


let is_op_bool : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bool op) <> None))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_33 -> (match (_82_33) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_42 = m
in (match (_82_42) with
| ((prefix, final), _82_39, _82_41) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_52 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _179_42 = (translate_module m)
in Some (_179_42)))
end)
with
| e -> begin
(

let _82_48 = (let _179_44 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_44))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_58 -> (match (_82_58) with
| (module_name, modul, _82_57) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _82_65 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Extraction_JavaScript_Ast.source_t Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_87); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_82_77, _82_79, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _82_74; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _82_71})::[]) -> begin
(

let rec find_return_type = (fun _82_3 -> (match (_82_3) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_82_96, _82_98, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _179_50 = (find_return_type t)
in (translate_type _179_50))
in (let _179_54 = (let _179_52 = (translate_expr expr ((name), (Some (t))) None)
in (FStar_All.pipe_right _179_52 (fun _179_51 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_51))))
in (FStar_All.pipe_right _179_54 (fun _179_53 -> Some (_179_53))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_116); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _82_109; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _82_106})::[]) -> begin
(

let t = (translate_type t)
in (let _179_58 = (let _179_56 = (translate_expr expr ((name), (Some (t))) None)
in (FStar_All.pipe_right _179_56 (fun _179_55 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_55))))
in (FStar_All.pipe_right _179_58 (fun _179_57 -> Some (_179_57)))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_134); FStar_Extraction_ML_Syntax.mllb_tysc = Some (_82_130); FStar_Extraction_ML_Syntax.mllb_add_unit = _82_128; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _82_125})::[]) -> begin
(let _179_62 = (let _179_60 = (translate_expr expr ((name), (None)) None)
in (FStar_All.pipe_right _179_60 (fun _179_59 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_59))))
in (FStar_All.pipe_right _179_62 (fun _179_61 -> Some (_179_61))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_82_141) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_144) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_147, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(let _179_68 = (let _179_66 = (let _179_64 = (let _179_63 = (translate_type t)
in ((((name), (None))), (None), (_179_63)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_64))
in (FStar_All.pipe_right _179_66 (fun _179_65 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_65))))
in (FStar_All.pipe_right _179_68 (fun _179_67 -> Some (_179_67))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_157, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let fields_t = (FStar_List.map (fun _82_168 -> (match (_82_168) with
| (n, t) -> begin
(let _179_70 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier (((n), (None)))), (_179_70)))
end)) fields)
in (let _179_73 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (None), (FStar_Extraction_JavaScript_Ast.JST_Object (((fields_t), ([]), ([]))))))) (fun _179_71 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_71)))
in (FStar_All.pipe_right _179_73 (fun _179_72 -> Some (_179_72)))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_171, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_DType (lfields))))::[]) -> begin
(

let fields_t = (fun fields -> (FStar_List.map (fun t -> (let _179_77 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_77)))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_185 -> (match (_82_185) with
| (n, l) -> begin
(let _179_82 = (let _179_81 = (let _179_80 = (let _179_79 = (fields_t l)
in ((_179_79), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_80))
in ((((n), (None))), (None), (_179_81)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_82))
end)) lfields)
in (

let lnames = (FStar_List.map (fun _82_189 -> (match (_82_189) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), ("")))
end)) lfields)
in (

let union_t = FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (None), (FStar_Extraction_JavaScript_Ast.JST_Union (lnames))))
in (let _179_86 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block (lfields_t)) (fun _179_84 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_84)))
in (FStar_All.pipe_right _179_86 (fun _179_85 -> Some (_179_85))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_193) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_196) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_199) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun e var stmt -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(match (stmt) with
| Some (v) -> begin
(let _179_96 = (let _179_95 = (let _179_94 = (let _179_93 = (let _179_92 = (let _179_91 = (let _179_90 = (translate_constant c)
in Some (_179_90))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_91)))
in (_179_92)::[])
in ((_179_93), (FStar_Extraction_JavaScript_Ast.JSV_Const)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_94))
in (_179_95)::(v)::[])
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_96))
end
| None -> begin
(let _179_101 = (let _179_100 = (let _179_99 = (let _179_98 = (let _179_97 = (translate_constant c)
in Some (_179_97))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_98)))
in (_179_99)::[])
in ((_179_100), (FStar_Extraction_JavaScript_Ast.JSV_Const)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_101))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_211) -> begin
(match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::(v)::[])
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((n), (None)))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_232); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], _82_227); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(let _179_103 = (let _179_102 = (translate_expr continuation var stmt)
in Some (_179_102))
in (translate_expr body ((name), (None)) _179_103))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_241) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_246; FStar_Extraction_ML_Syntax.loc = _82_244}, args) when (is_op_bin op) -> begin
(match (stmt) with
| Some (v) -> begin
(let _179_116 = (let _179_115 = (let _179_114 = (let _179_113 = (let _179_112 = (let _179_111 = (let _179_110 = (let _179_109 = (let _179_108 = (FStar_Util.must (mk_op_bin op))
in (let _179_107 = (let _179_104 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_104))
in (let _179_106 = (let _179_105 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_105))
in ((_179_108), (_179_107), (_179_106)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_109))
in Some (_179_110))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_111)))
in (_179_112)::[])
in ((_179_113), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_114))
in (_179_115)::(v)::[])
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_116))
end
| None -> begin
(let _179_127 = (let _179_126 = (let _179_125 = (let _179_124 = (let _179_123 = (let _179_122 = (let _179_121 = (FStar_Util.must (mk_op_bin op))
in (let _179_120 = (let _179_117 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_117))
in (let _179_119 = (let _179_118 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_118))
in ((_179_121), (_179_120), (_179_119)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_122))
in Some (_179_123))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_124)))
in (_179_125)::[])
in ((_179_126), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_127))
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_262; FStar_Extraction_ML_Syntax.loc = _82_260}, args) when (is_op_bool op) -> begin
(match (stmt) with
| Some (v) -> begin
(let _179_140 = (let _179_139 = (let _179_138 = (let _179_137 = (let _179_136 = (let _179_135 = (let _179_134 = (let _179_133 = (let _179_132 = (FStar_Util.must (mk_op_bool op))
in (let _179_131 = (let _179_128 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_128))
in (let _179_130 = (let _179_129 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_129))
in ((_179_132), (_179_131), (_179_130)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_133))
in Some (_179_134))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_135)))
in (_179_136)::[])
in ((_179_137), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_138))
in (_179_139)::(v)::[])
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_140))
end
| None -> begin
(let _179_151 = (let _179_150 = (let _179_149 = (let _179_148 = (let _179_147 = (let _179_146 = (let _179_145 = (FStar_Util.must (mk_op_bool op))
in (let _179_144 = (let _179_141 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_141))
in (let _179_143 = (let _179_142 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_142))
in ((_179_145), (_179_144), (_179_143)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_146))
in Some (_179_147))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_148)))
in (_179_149)::[])
in ((_179_150), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_151))
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _82_278; FStar_Extraction_ML_Syntax.loc = _82_276}, args) -> begin
(

let args_t = (FStar_List.map translate_expr_app args)
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (args_t)))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::(v)::[])
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (args_t)))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
end))
end
| FStar_Extraction_ML_Syntax.MLE_App (_82_292) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_295, fields) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_82_300, path) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args_t = (FStar_List.map (fun _82_313 -> (match (_82_313) with
| ((n, _82_310), t) -> begin
FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (None)))
end)) args)
in (

let fv = (FStar_Absyn_Util.gensym ())
in (

let body_t = (translate_expr body ((fv), (None)) (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv), (None))))))))
in (

let newFun = FStar_Extraction_JavaScript_Ast.JSE_Function (((None), (args_t), (FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((body_t)::[])), (None), (None)))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (newFun))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::(v)::[])
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (newFun))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_82_322) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_82_325) -> begin
(match (stmt) with
| Some (v) -> begin
(let _179_159 = (let _179_158 = (let _179_157 = (let _179_156 = (let _179_155 = (let _179_154 = (let _179_153 = (translate_expr_app e)
in Some (_179_153))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_154)))
in (_179_155)::[])
in ((_179_156), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_157))
in (_179_158)::(v)::[])
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_159))
end
| None -> begin
(let _179_164 = (let _179_163 = (let _179_162 = (let _179_161 = (let _179_160 = (translate_expr_app e)
in Some (_179_160))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_161)))
in (_179_162)::[])
in ((_179_163), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_164))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (_82_331) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Seq]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_82_334, e1, e2) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_340) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_343) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(translate_expr in_e var stmt)
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let depth = (FStar_List.length lb)
in (

let r = (FStar_Absyn_Util.gensym ())
in (let _179_166 = (let _179_165 = (translate_match (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((r), (None)))) lb var depth)
in Some (_179_165))
in (translate_expr e_in ((r), (None)) _179_166))))
end))
and translate_expr_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_361) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_82_365, name) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_372; FStar_Extraction_ML_Syntax.loc = _82_370}, args) when (is_op_bin op) -> begin
(let _179_173 = (let _179_172 = (FStar_Util.must (mk_op_bin op))
in (let _179_171 = (let _179_168 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_168))
in (let _179_170 = (let _179_169 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_169))
in ((_179_172), (_179_171), (_179_170)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_173))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _82_385; FStar_Extraction_ML_Syntax.loc = _82_383}, args) -> begin
(let _179_175 = (let _179_174 = (FStar_List.map translate_expr_app args)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (_179_174)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_175))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let arnity = (FStar_List.length lexp)
in (

let create_field = (fun i v -> (let _179_185 = (let _179_184 = (let _179_182 = (let _179_181 = (let _179_180 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_180))
in ((_179_181), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_182))
in (let _179_183 = (translate_expr_app v)
in ((_179_184), (_179_183), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_185)))
in (

let create_fields = (FStar_List.mapi (fun i x -> (create_field i x)) lexp)
in (let _179_197 = (let _179_196 = (let _179_195 = (let _179_194 = (let _179_193 = (let _179_192 = (let _179_191 = (let _179_190 = (let _179_189 = (let _179_188 = (FStar_Util.int32_of_int arnity)
in (FStar_Util.float_of_int32 _179_188))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_189))
in ((_179_190), ("")))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_191))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (_179_192), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_193))
in (_179_194)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_195)
in (FStar_List.append _179_196 create_fields))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_197)))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (c, lexpr) -> begin
(let _179_204 = (let _179_203 = (let _179_202 = (let _179_201 = (let _179_200 = (let _179_199 = (let _179_198 = (FStar_List.map translate_expr_app lexpr)
in Some (_179_198))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_199))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_200), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_201))
in (_179_202)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ((FStar_Extraction_ML_Syntax.string_of_mlpath c))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_203)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_204))
end
| _82_408 -> begin
(FStar_All.failwith "todo: translation of expressions")
end))
and translate_match : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun r lb x d -> (

let v1 = (FStar_Absyn_Util.gensym ())
in (

let _82_417 = (FStar_List.nth lb ((FStar_List.length lb) - d))
in (match (_82_417) with
| (p, guard, expr_r) -> begin
(

let _82_420 = ((FStar_Extraction_JavaScript_Ast.JSE_This), (None))
in (match (_82_420) with
| (pattern_tran, pattern_fv) -> begin
(match (guard) with
| Some (v) -> begin
(

let f1 = (FStar_Absyn_Util.gensym ())
in (

let stmt_true = (match (pattern_fv) with
| Some (fv) -> begin
(let _179_211 = (let _179_210 = (let _179_209 = (translate_expr v ((f1), (None)) None)
in (_179_209)::[])
in (fv)::_179_210)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_211))
end
| None -> begin
(translate_expr v ((f1), (None)) None)
end)
in (

let if_stmt = (let _179_218 = (let _179_217 = (let _179_216 = (let _179_215 = (let _179_214 = (translate_expr expr_r x (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (x))))))
in (let _179_213 = if (d = (Prims.parse_int "1")) then begin
None
end else begin
(let _179_212 = (translate_match r lb x (d - (Prims.parse_int "1")))
in Some (_179_212))
end
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((f1), (None)))), (_179_214), (_179_213))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_215))
in (_179_216)::[])
in (stmt_true)::_179_217)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_218))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((v1), (None)))), (Some (FStar_Extraction_JavaScript_Ast.JSE_Call (((pattern_tran), ((r)::[])))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::(FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((v1), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean)))))))), (if_stmt), (None))))::[]))))
end
| None -> begin
(

let stmt_true = (match (pattern_fv) with
| Some (fv) -> begin
(let _179_221 = (let _179_220 = (let _179_219 = (translate_expr expr_r x (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (x))))))
in (_179_219)::[])
in (fv)::_179_220)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_221))
end
| None -> begin
(translate_expr expr_r x (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (x))))))
end)
in (let _179_227 = (let _179_226 = (let _179_225 = (let _179_224 = (let _179_223 = if (d = (Prims.parse_int "1")) then begin
None
end else begin
(let _179_222 = (translate_match r lb x (d - (Prims.parse_int "1")))
in Some (_179_222))
end
in ((FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((v1), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean)))))))), (stmt_true), (_179_223)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_224))
in (_179_225)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((v1), (None)))), (Some (FStar_Extraction_JavaScript_Ast.JSE_Call (((pattern_tran), ((r)::[])))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::_179_226)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_227)))
end)
end))
end))))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_82_440)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_447) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_452) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, None) -> begin
(let _179_233 = (let _179_232 = (let _179_231 = (let _179_230 = (let _179_229 = (FStar_Util.int_of_string s)
in (FStar_Util.int32_of_int _179_229))
in (FStar_Util.float_of_int32 _179_230))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_231))
in ((_179_232), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_233))
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Top]")
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_82_463) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_467, t2) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Fun]")
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
FStar_Extraction_JavaScript_Ast.JST_Void
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
FStar_Extraction_JavaScript_Ast.JST_Boolean
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.int") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.nat")) -> begin
FStar_Extraction_JavaScript_Ast.JST_Number
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.string") -> begin
FStar_Extraction_JavaScript_Ast.JST_String
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_82_488, (path, type_name)) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Named]")
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_82_495) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))




