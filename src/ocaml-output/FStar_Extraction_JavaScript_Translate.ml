
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
| _82_23 -> begin
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
| _82_29 -> begin
None
end))


let is_op_bool : Prims.string  ->  Prims.bool = (fun op -> ((mk_op_bool op) <> None))


let float_of_int : Prims.int  ->  FStar_BaseTypes.float = (fun i -> (FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)))


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
in (let _179_61 = (translate_module m)
in Some (_179_61)))
end)
with
| e -> begin
(

let _82_48 = (let _179_63 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_63))
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
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_80); FStar_Extraction_ML_Syntax.mllb_tysc = Some (_82_76); FStar_Extraction_ML_Syntax.mllb_add_unit = _82_74; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _82_71})::[]) -> begin
(

let var = ((name), (None))
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (let _179_73 = (let _179_71 = (let _179_69 = (let _179_68 = (let _179_67 = (translate_expr expr var None)
in (_179_67)::[])
in (decl_v)::_179_68)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_69))
in (FStar_All.pipe_right _179_71 (fun _179_70 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_70))))
in (FStar_All.pipe_right _179_73 (fun _179_72 -> Some (_179_72))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_82_89) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_92) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_95, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(let _179_79 = (let _179_77 = (let _179_75 = (let _179_74 = (translate_type t)
in ((((name), (None))), (None), (_179_74)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_75))
in (FStar_All.pipe_right _179_77 (fun _179_76 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_76))))
in (FStar_All.pipe_right _179_79 (fun _179_78 -> Some (_179_78))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_105, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let fields_t = (FStar_List.map (fun _82_116 -> (match (_82_116) with
| (n, t) -> begin
(let _179_81 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier (((n), (None)))), (_179_81)))
end)) fields)
in (let _179_84 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (None), (FStar_Extraction_JavaScript_Ast.JST_Object (((fields_t), ([]), ([]))))))) (fun _179_82 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_82)))
in (FStar_All.pipe_right _179_84 (fun _179_83 -> Some (_179_83)))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_119, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_DType (lfields))))::[]) -> begin
(

let fields_t = (fun fields -> (FStar_List.map (fun t -> (let _179_88 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_88)))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_133 -> (match (_82_133) with
| (n, l) -> begin
(let _179_93 = (let _179_92 = (let _179_91 = (let _179_90 = (fields_t l)
in ((_179_90), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_91))
in ((((n), (None))), (None), (_179_92)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_93))
end)) lfields)
in (

let lnames = (FStar_List.map (fun _82_137 -> (match (_82_137) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), ("")))
end)) lfields)
in (

let union_t = FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (None), (FStar_Extraction_JavaScript_Ast.JST_Union (lnames))))
in (let _179_97 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block (lfields_t)) (fun _179_95 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_95)))
in (FStar_All.pipe_right _179_97 (fun _179_96 -> Some (_179_96))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_82_141) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_144) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_147) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t Prims.option  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun e var stmt -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let com = (let _179_103 = (let _179_102 = (let _179_101 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_101)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_102))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_103))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((com)::(v)::[])
end
| None -> begin
com
end))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_160) -> begin
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
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_186); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], _82_181); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let tr_e = (let _179_105 = (let _179_104 = (translate_expr continuation var stmt)
in Some (_179_104))
in (translate_expr body ((name), (None)) _179_105))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(tr_e)::[])))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_197) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_202; FStar_Extraction_ML_Syntax.loc = _82_200}, args) when (is_op_bin op) -> begin
(

let c = (let _179_114 = (let _179_113 = (let _179_112 = (let _179_111 = (let _179_110 = (FStar_Util.must (mk_op_bin op))
in (let _179_109 = (let _179_106 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_106))
in (let _179_108 = (let _179_107 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_107))
in ((_179_110), (_179_109), (_179_108)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_111))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_112)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_113))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_114))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_219; FStar_Extraction_ML_Syntax.loc = _82_217}, args) when (is_op_bool op) -> begin
(

let c = (let _179_123 = (let _179_122 = (let _179_121 = (let _179_120 = (let _179_119 = (FStar_Util.must (mk_op_bool op))
in (let _179_118 = (let _179_115 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_115))
in (let _179_117 = (let _179_116 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_116))
in ((_179_119), (_179_118), (_179_117)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_120))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_121)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_122))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_123))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _82_236; FStar_Extraction_ML_Syntax.loc = _82_234}, args) -> begin
(

let args_t = (FStar_List.map translate_expr_app args)
in (

let c = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (args_t)))))))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end)))
end
| FStar_Extraction_ML_Syntax.MLE_App (_82_251) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_254, fields) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_82_259, path) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args_t = (FStar_List.map (fun _82_272 -> (match (_82_272) with
| ((n, _82_269), t) -> begin
FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (None)))
end)) args)
in (

let fv = (FStar_Absyn_Util.gensym ())
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let body_t = (translate_expr body ((fv), (None)) (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv), (None))))))))
in (

let newFun = FStar_Extraction_JavaScript_Ast.JSE_Function (((None), (args_t), (FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((decl_v)::(body_t)::[])), (None), (None)))
in (

let c = FStar_Extraction_JavaScript_Ast.JSS_Expression (FStar_Extraction_JavaScript_Ast.JSE_Assignment (((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (newFun))))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_82_283) -> begin
(

let c = (let _179_127 = (let _179_126 = (let _179_125 = (translate_expr_app e)
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
| FStar_Extraction_ML_Syntax.MLE_Tuple (_82_290) -> begin
(

let c = (let _179_130 = (let _179_129 = (let _179_128 = (translate_expr_app e)
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_128)))
in FStar_Extraction_JavaScript_Ast.JSE_Assignment (_179_129))
in FStar_Extraction_JavaScript_Ast.JSS_Expression (_179_130))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (_82_297) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Seq]")
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, s1, s2) -> begin
(

let fv_t = (FStar_Absyn_Util.gensym ())
in (

let s2_tr = (match (s2) with
| Some (v) -> begin
(let _179_131 = (translate_expr v var None)
in Some (_179_131))
end
| None -> begin
None
end)
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_t), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let c = (let _179_135 = (let _179_134 = (let _179_133 = (let _179_132 = (translate_expr s1 var None)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_t), (None)))), (_179_132), (s2_tr)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_133))
in Some (_179_134))
in (translate_expr cond ((fv_t), (None)) _179_135))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::(v)::[])
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::[])
end)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_315) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_318) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (in_e, t_from, t_to) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end
| FStar_Extraction_ML_Syntax.MLE_Match (e_in, lb) -> begin
(

let depth = (FStar_List.length lb)
in (

let fv_x = "_x"
in (

let decl_v = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((fv_x), (None)))), (None)))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let)))
in (

let c = (let _179_137 = (let _179_136 = (translate_match lb (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv_x), (None)))) depth var)
in Some (_179_136))
in (translate_expr e_in ((fv_x), (None)) _179_137))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::(v)::[])
end
| None -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((decl_v)::(c)::[])
end)))))
end))
and translate_expr_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_341) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_82_345, name) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_352; FStar_Extraction_ML_Syntax.loc = _82_350}, args) when (is_op_bin op) -> begin
(let _179_144 = (let _179_143 = (FStar_Util.must (mk_op_bin op))
in (let _179_142 = (let _179_139 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_139))
in (let _179_141 = (let _179_140 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_140))
in ((_179_143), (_179_142), (_179_141)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_144))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _82_365; FStar_Extraction_ML_Syntax.loc = _82_363}, args) -> begin
(let _179_146 = (let _179_145 = (FStar_List.map translate_expr_app args)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (_179_145)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_146))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let arity = (FStar_List.length lexp)
in (

let create_field = (fun i v -> (let _179_156 = (let _179_155 = (let _179_153 = (let _179_152 = (let _179_151 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_151))
in ((_179_152), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_153))
in (let _179_154 = (translate_expr_app v)
in ((_179_155), (_179_154), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_156)))
in (

let create_fields = (FStar_List.mapi (fun i x -> (create_field i x)) lexp)
in FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((FStar_Util.float_of_int32 (FStar_Util.int32_of_int arity)))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields)))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (c, lexpr) -> begin
(let _179_165 = (let _179_164 = (let _179_163 = (let _179_162 = (let _179_161 = (let _179_160 = (let _179_159 = (FStar_List.map translate_expr_app lexpr)
in Some (_179_159))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_160))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_161), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_162))
in (_179_163)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ((FStar_Extraction_ML_Syntax.string_of_mlpath c))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_164)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_165))
end
| _82_388 -> begin
(FStar_All.failwith "todo: translation of expressions")
end))
and translate_match : FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  Prims.int  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lb fv_x d var -> if (d = (Prims.parse_int "0")) then begin
FStar_Extraction_JavaScript_Ast.JSS_Throw (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("This value doesn\'t match!")), (""))))
end else begin
(

let _82_396 = (FStar_List.nth lb ((FStar_List.length lb) - d))
in (match (_82_396) with
| (p, guard, expr_r) -> begin
(let _179_171 = (translate_expr expr_r var None)
in (let _179_170 = (translate_match lb fv_x (d - (Prims.parse_int "1")) var)
in (translate_pat_guard ((p), (guard)) fv_x _179_171 _179_170)))
end))
end)
and translate_pat_guard : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option)  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun _82_399 fv_x s1 s2 -> (match (_82_399) with
| (p, guard) -> begin
(match (guard) with
| None -> begin
(translate_pat p fv_x s1 s2)
end
| Some (v_guard) -> begin
(

let cond_stmt = (let _179_177 = (let _179_176 = (translate_expr_app v_guard)
in ((_179_176), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_177))
in (translate_pat p fv_x cond_stmt s2))
end)
end))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun p fv_x s1 s2 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_413) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (fv_x))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Let))))::(s1)::[])
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_185 = (let _179_184 = (let _179_183 = (let _179_182 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (fv_x), (_179_182)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_183))
in ((_179_184), (s1), (Some (s2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_185))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (c, lp) -> begin
(

let if_true = (match ((FStar_List.length lp)) with
| _179_186 when (_179_186 = (Prims.parse_int "0")) -> begin
s1
end
| _179_187 when (_179_187 = (Prims.parse_int "1")) -> begin
(let _179_188 = (FStar_List.nth lp (Prims.parse_int "0"))
in (translate_pat _179_188 (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) s1 s2))
end
| _82_426 -> begin
(translate_p_ctor lp (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None))))))) s1 s2)
end)
in FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_Equal), (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String)))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ((FStar_Extraction_ML_Syntax.string_of_mlpath c))), (""))))))), (if_true), (Some (s2)))))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_82_429) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_82_432) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(translate_p_tuple lp (FStar_List.length lp) fv_x s1 s2)
end))
and translate_p_ctor : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp fv_x s1 s2 -> (match (lp) with
| (x)::[] -> begin
(translate_pat x fv_x s1 s2)
end
| (hd)::tl -> begin
(let _179_193 = (translate_p_ctor tl (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "1")))), ("")))))))) s1 s2)
in (translate_pat hd (FStar_Extraction_JavaScript_Ast.JSE_Member (((fv_x), (FStar_Extraction_JavaScript_Ast.JSPM_Expression (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number ((float_of_int (Prims.parse_int "0")))), ("")))))))) _179_193 s2))
end
| [] -> begin
(FStar_All.failwith "Empty list in pattern matching")
end))
and translate_p_tuple : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun lp d fv_x s1 s2 -> (

let n = (FStar_List.length lp)
in if (d = (Prims.parse_int "1")) then begin
(let _179_205 = (FStar_List.nth lp (n - d))
in (let _179_204 = (let _179_203 = (let _179_202 = (let _179_201 = (let _179_200 = (let _179_199 = (FStar_Util.string_of_int (n - d))
in (Prims.strcat "_f" _179_199))
in ((_179_200), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_201))
in ((fv_x), (_179_202)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_203))
in (translate_pat _179_205 _179_204 s1 s2)))
end else begin
(let _179_213 = (FStar_List.nth lp (n - d))
in (let _179_212 = (let _179_210 = (let _179_209 = (let _179_208 = (let _179_207 = (let _179_206 = (FStar_Util.string_of_int (n - d))
in (Prims.strcat "_f" _179_206))
in ((_179_207), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_208))
in ((fv_x), (_179_209)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_210))
in (let _179_211 = (translate_p_tuple lp (d - (Prims.parse_int "1")) fv_x s1 s2)
in (translate_pat _179_213 _179_212 _179_211 s2))))
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_82_458)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_465) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_470) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, None) -> begin
(let _179_218 = (let _179_217 = (let _179_216 = (let _179_215 = (FStar_Util.int_of_string s)
in (float_of_int _179_215))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_216))
in ((_179_217), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_218))
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Top]")
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_82_481) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_485, t2) -> begin
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
| FStar_Extraction_ML_Syntax.MLTY_Named (_82_506, (path, type_name)) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Named]")
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_82_513) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))




