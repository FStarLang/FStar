
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
in (let _179_46 = (translate_module m)
in Some (_179_46)))
end)
with
| e -> begin
(

let _82_48 = (let _179_48 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _179_48))
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

let t = (let _179_54 = (find_return_type t)
in (translate_type _179_54))
in (let _179_58 = (let _179_56 = (translate_expr expr ((name), (Some (t))) None)
in (FStar_All.pipe_right _179_56 (fun _179_55 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_55))))
in (FStar_All.pipe_right _179_58 (fun _179_57 -> Some (_179_57))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_116); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _82_109; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _82_106})::[]) -> begin
(

let t = (translate_type t)
in (let _179_62 = (let _179_60 = (translate_expr expr ((name), (Some (t))) None)
in (FStar_All.pipe_right _179_60 (fun _179_59 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_59))))
in (FStar_All.pipe_right _179_62 (fun _179_61 -> Some (_179_61)))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_134); FStar_Extraction_ML_Syntax.mllb_tysc = Some (_82_130); FStar_Extraction_ML_Syntax.mllb_add_unit = _82_128; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _82_125})::[]) -> begin
(let _179_66 = (let _179_64 = (translate_expr expr ((name), (None)) None)
in (FStar_All.pipe_right _179_64 (fun _179_63 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_63))))
in (FStar_All.pipe_right _179_66 (fun _179_65 -> Some (_179_65))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_82_141) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_144) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_147, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(let _179_72 = (let _179_70 = (let _179_68 = (let _179_67 = (translate_type t)
in ((((name), (None))), (None), (_179_67)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_68))
in (FStar_All.pipe_right _179_70 (fun _179_69 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_69))))
in (FStar_All.pipe_right _179_72 (fun _179_71 -> Some (_179_71))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_157, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let fields_t = (FStar_List.map (fun _82_168 -> (match (_82_168) with
| (n, t) -> begin
(let _179_74 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier (((n), (None)))), (_179_74)))
end)) fields)
in (let _179_77 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (None), (FStar_Extraction_JavaScript_Ast.JST_Object (((fields_t), ([]), ([]))))))) (fun _179_75 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_75)))
in (FStar_All.pipe_right _179_77 (fun _179_76 -> Some (_179_76)))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_171, name, [], Some (FStar_Extraction_ML_Syntax.MLTD_DType (lfields))))::[]) -> begin
(

let fields_t = (fun fields -> (FStar_List.map (fun t -> (let _179_81 = (translate_type t)
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_81)))) fields))
in (

let lfields_t = (FStar_List.map (fun _82_185 -> (match (_82_185) with
| (n, l) -> begin
(let _179_86 = (let _179_85 = (let _179_84 = (let _179_83 = (fields_t l)
in ((_179_83), ([]), ([])))
in FStar_Extraction_JavaScript_Ast.JST_Object (_179_84))
in ((((n), (None))), (None), (_179_85)))
in FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (_179_86))
end)) lfields)
in (

let lnames = (FStar_List.map (fun _82_189 -> (match (_82_189) with
| (n, l) -> begin
FStar_Extraction_JavaScript_Ast.JST_StringLiteral (((n), ("")))
end)) lfields)
in (

let union_t = FStar_Extraction_JavaScript_Ast.JSS_TypeAlias (((((name), (None))), (None), (FStar_Extraction_JavaScript_Ast.JST_Union (lnames))))
in (let _179_90 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSS_Block (lfields_t)) (fun _179_88 -> FStar_Extraction_JavaScript_Ast.JS_Statement (_179_88)))
in (FStar_All.pipe_right _179_90 (fun _179_89 -> Some (_179_89))))))))
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
(

let com = (let _179_98 = (let _179_97 = (let _179_96 = (let _179_95 = (let _179_94 = (translate_constant c)
in Some (_179_94))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_95)))
in (_179_96)::[])
in ((_179_97), (FStar_Extraction_JavaScript_Ast.JSV_Const)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_98))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((com)::(v)::[])
end
| None -> begin
com
end))
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_212) -> begin
(

let c = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Name (path, n) -> begin
FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((n), (None)))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_234); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], _82_229); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(let _179_100 = (let _179_99 = (translate_expr continuation var stmt)
in Some (_179_99))
in (translate_expr body ((name), (None)) _179_100))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_243) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_248; FStar_Extraction_ML_Syntax.loc = _82_246}, args) when (is_op_bin op) -> begin
(

let c = (let _179_111 = (let _179_110 = (let _179_109 = (let _179_108 = (let _179_107 = (let _179_106 = (let _179_105 = (FStar_Util.must (mk_op_bin op))
in (let _179_104 = (let _179_101 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_101))
in (let _179_103 = (let _179_102 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_102))
in ((_179_105), (_179_104), (_179_103)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_106))
in Some (_179_107))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_108)))
in (_179_109)::[])
in ((_179_110), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_111))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_265; FStar_Extraction_ML_Syntax.loc = _82_263}, args) when (is_op_bool op) -> begin
(

let c = (let _179_122 = (let _179_121 = (let _179_120 = (let _179_119 = (let _179_118 = (let _179_117 = (let _179_116 = (FStar_Util.must (mk_op_bool op))
in (let _179_115 = (let _179_112 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_112))
in (let _179_114 = (let _179_113 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_113))
in ((_179_116), (_179_115), (_179_114)))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_117))
in Some (_179_118))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_119)))
in (_179_120)::[])
in ((_179_121), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_122))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _82_282; FStar_Extraction_ML_Syntax.loc = _82_280}, args) -> begin
(

let args_t = (FStar_List.map translate_expr_app args)
in (

let c = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (FStar_Extraction_JavaScript_Ast.JSE_Call (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (args_t)))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end)))
end
| FStar_Extraction_ML_Syntax.MLE_App (_82_297) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_300, fields) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_82_305, path) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (args, body) -> begin
(

let args_t = (FStar_List.map (fun _82_318 -> (match (_82_318) with
| ((n, _82_315), t) -> begin
FStar_Extraction_JavaScript_Ast.JGP_Identifier (((n), (None)))
end)) args)
in (

let fv = (FStar_Absyn_Util.gensym ())
in (

let body_t = (translate_expr body ((fv), (None)) (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((fv), (None))))))))
in (

let newFun = FStar_Extraction_JavaScript_Ast.JSE_Function (((None), (args_t), (FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((body_t)::[])), (None), (None)))
in (

let c = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (Some (newFun))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_82_328) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_82_331) -> begin
(

let c = (let _179_128 = (let _179_127 = (let _179_126 = (let _179_125 = (let _179_124 = (translate_expr_app e)
in Some (_179_124))
in ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (var)), (_179_125)))
in (_179_126)::[])
in ((_179_127), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_128))
in (match (stmt) with
| Some (v) -> begin
FStar_Extraction_JavaScript_Ast.JSS_Block ((c)::(v)::[])
end
| None -> begin
c
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (_82_338) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Seq]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_82_341, e1, e2) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_347) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_350) -> begin
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
in (let _179_130 = (let _179_129 = (translate_match (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((r), (None)))) lb var depth)
in Some (_179_129))
in (translate_expr e_in ((r), (None)) _179_130))))
end))
and translate_expr_app : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_368) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_82_372, name) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_379; FStar_Extraction_ML_Syntax.loc = _82_377}, args) when (is_op_bin op) -> begin
(let _179_137 = (let _179_136 = (FStar_Util.must (mk_op_bin op))
in (let _179_135 = (let _179_132 = (FStar_List.nth args (Prims.parse_int "0"))
in (translate_expr_app _179_132))
in (let _179_134 = (let _179_133 = (FStar_List.nth args (Prims.parse_int "1"))
in (translate_expr_app _179_133))
in ((_179_136), (_179_135), (_179_134)))))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_137))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _82_392; FStar_Extraction_ML_Syntax.loc = _82_390}, args) -> begin
(let _179_139 = (let _179_138 = (FStar_List.map translate_expr_app args)
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((function_name), (None)))), (_179_138)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_139))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (lexp) -> begin
(

let arity = (FStar_List.length lexp)
in (

let create_field = (fun i v -> (let _179_149 = (let _179_148 = (let _179_146 = (let _179_145 = (let _179_144 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_144))
in ((_179_145), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_146))
in (let _179_147 = (translate_expr_app v)
in ((_179_148), (_179_147), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_149)))
in (

let create_fields = (FStar_List.mapi (fun i x -> (create_field i x)) lexp)
in (let _179_161 = (let _179_160 = (let _179_159 = (let _179_158 = (let _179_157 = (let _179_156 = (let _179_155 = (let _179_154 = (let _179_153 = (let _179_152 = (FStar_Util.int32_of_int arity)
in (FStar_Util.float_of_int32 _179_152))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_153))
in ((_179_154), ("")))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_155))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_arity"), (Some (FStar_Extraction_JavaScript_Ast.JST_Number))))), (_179_156), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_157))
in (_179_158)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ("Tuple")), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_159)
in (FStar_List.append _179_160 create_fields))
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_161)))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (c, lexpr) -> begin
(let _179_168 = (let _179_167 = (let _179_166 = (let _179_165 = (let _179_164 = (let _179_163 = (let _179_162 = (FStar_List.map translate_expr_app lexpr)
in Some (_179_162))
in FStar_Extraction_JavaScript_Ast.JSE_Array (_179_163))
in ((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_value"), (None)))), (_179_164), (FStar_Extraction_JavaScript_Ast.JSO_Init)))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_165))
in (_179_166)::[])
in (FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_tag"), (Some (FStar_Extraction_JavaScript_Ast.JST_String))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ((FStar_Extraction_ML_Syntax.string_of_mlpath c))), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::_179_167)
in FStar_Extraction_JavaScript_Ast.JSE_Object (_179_168))
end
| _82_415 -> begin
(FStar_All.failwith "todo: translation of expressions")
end))
and translate_match : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  (Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option)  ->  Prims.int  ->  FStar_Extraction_JavaScript_Ast.statement_t = (fun r lb x d -> (

let v1 = (FStar_Absyn_Util.gensym ())
in (

let _82_424 = (FStar_List.nth lb ((FStar_List.length lb) - d))
in (match (_82_424) with
| (p, guard, expr_r) -> begin
(

let _82_427 = (translate_pat p v1)
in (match (_82_427) with
| (pattern_tran, pattern_fv) -> begin
(match (guard) with
| Some (v) -> begin
(

let f1 = (FStar_Absyn_Util.gensym ())
in (

let stmt_true = (match (pattern_fv) with
| Some (fv) -> begin
(let _179_175 = (let _179_174 = (let _179_173 = (translate_expr v ((f1), (None)) None)
in (_179_173)::[])
in (fv)::_179_174)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_175))
end
| None -> begin
(translate_expr v ((f1), (None)) None)
end)
in (

let if_stmt = (let _179_182 = (let _179_181 = (let _179_180 = (let _179_179 = (let _179_178 = (translate_expr expr_r x (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (x))))))
in (let _179_177 = if (d = (Prims.parse_int "1")) then begin
None
end else begin
(let _179_176 = (translate_match r lb x (d - (Prims.parse_int "1")))
in Some (_179_176))
end
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((f1), (None)))), (_179_178), (_179_177))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_179))
in (_179_180)::[])
in (stmt_true)::_179_181)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_182))
in FStar_Extraction_JavaScript_Ast.JSS_Block ((FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((v1), (None)))), (Some (FStar_Extraction_JavaScript_Ast.JSE_Call (((pattern_tran), ((r)::[])))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::(FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((v1), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean)))))))), (if_stmt), (None))))::[]))))
end
| None -> begin
(

let stmt_true = (match (pattern_fv) with
| Some (fv) -> begin
(let _179_185 = (let _179_184 = (let _179_183 = (translate_expr expr_r x (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (x))))))
in (_179_183)::[])
in (fv)::_179_184)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_185))
end
| None -> begin
(translate_expr expr_r x (Some (FStar_Extraction_JavaScript_Ast.JSS_Return (Some (FStar_Extraction_JavaScript_Ast.JSE_Identifier (x))))))
end)
in (let _179_191 = (let _179_190 = (let _179_189 = (let _179_188 = (let _179_187 = if (d = (Prims.parse_int "1")) then begin
None
end else begin
(let _179_186 = (translate_match r lb x (d - (Prims.parse_int "1")))
in Some (_179_186))
end
in ((FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((v1), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean)))))))), (stmt_true), (_179_187)))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_188))
in (_179_189)::[])
in (FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((v1), (None)))), (Some (FStar_Extraction_JavaScript_Ast.JSE_Call (((pattern_tran), ((r)::[])))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var))))::_179_190)
in FStar_Extraction_JavaScript_Ast.JSS_Block (_179_191)))
end)
end))
end))))
and translate_pat : FStar_Extraction_ML_Syntax.mlpattern  ->  Prims.string  ->  (FStar_Extraction_JavaScript_Ast.expression_t * FStar_Extraction_JavaScript_Ast.statement_t Prims.option) = (fun p v1 -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_445) -> begin
(

let body = (let _179_196 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (true)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::(FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_x"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (FStar_Extraction_JavaScript_Ast.JSE_Identifier (((name), (None)))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[])) (fun _179_194 -> Some (_179_194)))
in (FStar_All.pipe_right _179_196 (fun _179_195 -> FStar_Extraction_JavaScript_Ast.JSS_Return (_179_195))))
in (

let createfv = FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((((((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None)))), (Some (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((v1), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_x"), (None))))))))))::[]), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in ((FStar_Extraction_JavaScript_Ast.JSE_Function (((None), ((FStar_Extraction_JavaScript_Ast.JGP_Identifier (((name), (None))))::[]), (FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((body)::[])), (None), (None)))), (Some (createfv)))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(

let ob1 = (let _179_199 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (true)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[])) (fun _179_197 -> Some (_179_197)))
in (FStar_All.pipe_right _179_199 (fun _179_198 -> FStar_Extraction_JavaScript_Ast.JSS_Return (_179_198))))
in (

let ob2 = (let _179_202 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (false)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[])) (fun _179_200 -> Some (_179_200)))
in (FStar_All.pipe_right _179_202 (fun _179_201 -> FStar_Extraction_JavaScript_Ast.JSS_Return (_179_201))))
in (let _179_211 = (let _179_210 = (let _179_209 = (let _179_208 = (let _179_207 = (let _179_206 = (let _179_205 = (let _179_204 = (let _179_203 = (translate_constant c)
in ((FStar_Extraction_JavaScript_Ast.JSB_Equal), (FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("_x"), (None)))), (_179_203)))
in FStar_Extraction_JavaScript_Ast.JSE_Binary (_179_204))
in ((_179_205), (ob1), (Some (ob2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_206))
in (_179_207)::[])
in FStar_Extraction_JavaScript_Ast.JS_BodyBlock (_179_208))
in ((None), ((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("_x"), (None))))::[]), (_179_209), (None), (None)))
in FStar_Extraction_JavaScript_Ast.JSE_Function (_179_210))
in ((_179_211), (None)))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (c, lp) -> begin
(

let _82_461 = (translate_constr lp v1)
in (match (_82_461) with
| (pattern_tr, fv) -> begin
(

let ob1 = (let _179_214 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Call (((pattern_tr), ((FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("e"), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_value"), (None)))))))::[])))) (fun _179_212 -> Some (_179_212)))
in (FStar_All.pipe_right _179_214 (fun _179_213 -> FStar_Extraction_JavaScript_Ast.JSS_Return (_179_213))))
in (

let ob2 = (let _179_217 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (false)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[])) (fun _179_215 -> Some (_179_215)))
in (FStar_All.pipe_right _179_217 (fun _179_216 -> FStar_Extraction_JavaScript_Ast.JSS_Return (_179_216))))
in ((FStar_Extraction_JavaScript_Ast.JSE_Function (((None), ((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("e"), (None))))::[]), (FStar_Extraction_JavaScript_Ast.JS_BodyBlock ((FStar_Extraction_JavaScript_Ast.JSS_If (((FStar_Extraction_JavaScript_Ast.JSE_Binary (((FStar_Extraction_JavaScript_Ast.JSB_Equal), (FStar_Extraction_JavaScript_Ast.JSE_Member (((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("e"), (None)))), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_tag"), (None))))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String ((FStar_Extraction_ML_Syntax.string_of_mlpath c))), (""))))))), (ob1), (Some (ob2)))))::[])), (None), (None)))), (None))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_82_465) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_82_468) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (lp) -> begin
(

let arnity = (FStar_List.length lp)
in (

let create_decl = (fun p1 i -> (

let _82_478 = (let _179_223 = (let _179_222 = (FStar_Util.string_of_int i)
in (Prims.strcat "_r" _179_222))
in (translate_pat p1 _179_223))
in (match (_82_478) with
| (pattern_tr, fv) -> begin
(let _179_241 = (let _179_240 = (let _179_239 = (let _179_238 = (let _179_237 = (let _179_226 = (let _179_225 = (let _179_224 = (FStar_Util.string_of_int i)
in (Prims.strcat "_r" _179_224))
in ((_179_225), (None)))
in FStar_Extraction_JavaScript_Ast.JGP_Identifier (_179_226))
in (let _179_236 = (let _179_235 = (let _179_234 = (let _179_233 = (let _179_232 = (let _179_231 = (let _179_230 = (let _179_229 = (let _179_228 = (let _179_227 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_227))
in ((_179_228), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_229))
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("e"), (None)))), (_179_230)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_231))
in (_179_232)::[])
in ((pattern_tr), (_179_233)))
in FStar_Extraction_JavaScript_Ast.JSE_Call (_179_234))
in Some (_179_235))
in ((_179_237), (_179_236))))
in (_179_238)::[])
in ((_179_239), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_240))
in ((_179_241), (fv)))
end)))
in (

let create_decls_fv = (FStar_List.mapi (fun i x -> (create_decl x i)) lp)
in (

let create_decls = (FStar_List.map Prims.fst create_decls_fv)
in (

let create_tmp_fv = (fun i -> (let _179_260 = (let _179_259 = (let _179_258 = (let _179_257 = (let _179_249 = (let _179_248 = (let _179_247 = (let _179_246 = (FStar_Util.string_of_int i)
in (Prims.strcat _179_246 "_x"))
in (Prims.strcat "_r" _179_247))
in ((_179_248), (None)))
in FStar_Extraction_JavaScript_Ast.JGP_Identifier (_179_249))
in (let _179_256 = (let _179_255 = (let _179_254 = (let _179_253 = (let _179_252 = (let _179_251 = (let _179_250 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_250))
in ((_179_251), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_252))
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (((v1), (None)))), (_179_253)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_254))
in Some (_179_255))
in ((_179_257), (_179_256))))
in (_179_258)::[])
in ((_179_259), (FStar_Extraction_JavaScript_Ast.JSV_Var)))
in FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (_179_260)))
in (

let create_tmp_fvs = (FStar_List.map create_tmp_fv (((Prims.parse_int "0"))::((Prims.parse_int "1"))::[]))
in (

let create_field_ob1 = (fun i -> (let _179_273 = (let _179_272 = (let _179_265 = (let _179_264 = (let _179_263 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_263))
in ((_179_264), (None)))
in FStar_Extraction_JavaScript_Ast.JSO_Identifier (_179_265))
in (let _179_271 = (let _179_270 = (let _179_269 = (let _179_268 = (let _179_267 = (let _179_266 = (FStar_Util.string_of_int i)
in (Prims.strcat "_r" _179_266))
in ((_179_267), (None)))
in FStar_Extraction_JavaScript_Ast.JSE_Identifier (_179_268))
in ((_179_269), (FStar_Extraction_JavaScript_Ast.JSPM_Identifier ((("_x"), (None))))))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_270))
in ((_179_272), (_179_271), (FStar_Extraction_JavaScript_Ast.JSO_Init))))
in FStar_Extraction_JavaScript_Ast.JSPO_Property (_179_273)))
in (

let create_fields_ob1 = (FStar_List.map create_field_ob1 (((Prims.parse_int "0"))::((Prims.parse_int "1"))::[]))
in (

let ob1 = (let _179_276 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_List.append ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (true)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[]) create_fields_ob1))) (fun _179_274 -> Some (_179_274)))
in (FStar_All.pipe_right _179_276 (fun _179_275 -> FStar_Extraction_JavaScript_Ast.JSS_Return (_179_275))))
in (

let ob2 = (let _179_279 = (FStar_All.pipe_right (FStar_Extraction_JavaScript_Ast.JSE_Object ((FStar_Extraction_JavaScript_Ast.JSPO_Property (((FStar_Extraction_JavaScript_Ast.JSO_Identifier ((("_valid"), (Some (FStar_Extraction_JavaScript_Ast.JST_Boolean))))), (FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (false)), ("")))), (FStar_Extraction_JavaScript_Ast.JSO_Init))))::[])) (fun _179_277 -> Some (_179_277)))
in (FStar_All.pipe_right _179_279 (fun _179_278 -> FStar_Extraction_JavaScript_Ast.JSS_Return (_179_278))))
in (

let rec if_cond = (fun i -> (let _179_294 = (let _179_293 = (let _179_286 = (let _179_285 = (let _179_284 = (let _179_283 = (let _179_282 = (FStar_Util.string_of_int i)
in (Prims.strcat "_f" _179_282))
in ((_179_283), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_284))
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("e"), (None)))), (_179_285)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_286))
in (let _179_292 = if (i = (arnity - (Prims.parse_int "2"))) then begin
(let _179_291 = (let _179_290 = (let _179_289 = (let _179_288 = (let _179_287 = (FStar_Util.string_of_int (i + (Prims.parse_int "1")))
in (Prims.strcat "_f" _179_287))
in ((_179_288), (None)))
in FStar_Extraction_JavaScript_Ast.JSPM_Identifier (_179_289))
in ((FStar_Extraction_JavaScript_Ast.JSE_Identifier ((("e"), (None)))), (_179_290)))
in FStar_Extraction_JavaScript_Ast.JSE_Member (_179_291))
end else begin
(if_cond (i + (Prims.parse_int "1")))
end
in ((FStar_Extraction_JavaScript_Ast.JSL_And), (_179_293), (_179_292))))
in FStar_Extraction_JavaScript_Ast.JSE_Logical (_179_294)))
in (let _179_302 = (let _179_301 = (let _179_300 = (let _179_299 = (let _179_298 = (let _179_297 = (let _179_296 = (let _179_295 = (if_cond (Prims.parse_int "0"))
in ((_179_295), (ob1), (Some (ob2))))
in FStar_Extraction_JavaScript_Ast.JSS_If (_179_296))
in (_179_297)::[])
in (FStar_List.append create_decls _179_298))
in FStar_Extraction_JavaScript_Ast.JS_BodyBlock (_179_299))
in ((None), ((FStar_Extraction_JavaScript_Ast.JGP_Identifier ((("e"), (None))))::[]), (_179_300), (None), (None)))
in FStar_Extraction_JavaScript_Ast.JSE_Function (_179_301))
in ((_179_302), (None))))))))))))))
end))
and translate_constr : FStar_Extraction_ML_Syntax.mlpattern Prims.list  ->  Prims.string  ->  (FStar_Extraction_JavaScript_Ast.expression_t * FStar_Extraction_JavaScript_Ast.statement_t Prims.option) = (fun lp v1 -> (FStar_All.failwith "todo: translation CTor"))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  FStar_Extraction_JavaScript_Ast.expression_t = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Null), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Boolean (b)), ("")))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_82_501)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (f) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_Number (f)), ((FStar_Util.string_of_float f))))
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_508) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
FStar_Extraction_JavaScript_Ast.JSE_Literal (((FStar_Extraction_JavaScript_Ast.JSV_String (s)), (s)))
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_513) -> begin
(FStar_All.failwith "todo: translate_const [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, None) -> begin
(let _179_310 = (let _179_309 = (let _179_308 = (let _179_307 = (let _179_306 = (FStar_Util.int_of_string s)
in (FStar_Util.int32_of_int _179_306))
in (FStar_Util.float_of_int32 _179_307))
in FStar_Extraction_JavaScript_Ast.JSV_Number (_179_308))
in ((_179_309), (s)))
in FStar_Extraction_JavaScript_Ast.JSE_Literal (_179_310))
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_JavaScript_Ast.typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Top]")
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_82_524) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_528, t2) -> begin
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
| FStar_Extraction_ML_Syntax.MLTY_Named (_82_549, (path, type_name)) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Named]")
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_82_556) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))




