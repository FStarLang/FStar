
open Prims
# 37 "FStar.Extraction.ML.Modul.fst"
let fail_exp = (fun lid t -> (let _157_16 = (let _157_15 = (let _157_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _157_13 = (let _157_12 = (FStar_Syntax_Syntax.iarg t)
in (let _157_11 = (let _157_10 = (let _157_9 = (let _157_8 = (let _157_7 = (let _157_6 = (let _157_5 = (let _157_4 = (let _157_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _157_3))
in (FStar_Bytes.string_as_unicode_bytes _157_4))
in (_157_5, FStar_Range.dummyRange))
in FStar_Const.Const_string (_157_6))
in FStar_Syntax_Syntax.Tm_constant (_157_7))
in (FStar_Syntax_Syntax.mk _157_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _157_9))
in (_157_10)::[])
in (_157_12)::_157_11))
in (_157_14, _157_13)))
in FStar_Syntax_Syntax.Tm_app (_157_15))
in (FStar_Syntax_Syntax.mk _157_16 None FStar_Range.dummyRange)))

# 44 "FStar.Extraction.ML.Modul.fst"
let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (
# 45 "FStar.Extraction.ML.Modul.fst"
let projecteeName = x.FStar_Ident.ident
in (
# 46 "FStar.Extraction.ML.Modul.fst"
let _73_16 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_73_16) with
| (prefix, constrName) -> begin
(
# 47 "FStar.Extraction.ML.Modul.fst"
let mangledName = (FStar_Ident.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Ident.idText) "___") projecteeName.FStar_Ident.idText))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

# 50 "FStar.Extraction.ML.Modul.fst"
let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)

# 56 "FStar.Extraction.ML.Modul.fst"
let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (FStar_Extraction_ML_UEnv.prependTick (FStar_Extraction_ML_UEnv.convIdent x.FStar_Syntax_Syntax.ppname)))

# 58 "FStar.Extraction.ML.Modul.fst"
let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _73_26 -> (match (_73_26) with
| (bv, _73_25) -> begin
(let _157_27 = (FStar_Extraction_ML_UEnv.extend_ty env bv (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((bv_as_ml_tyvar bv)))))
in (_157_27, (bv_as_ml_tyvar bv)))
end)) env bs))

# 68 "FStar.Extraction.ML.Modul.fst"
let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env lid quals def -> (
# 69 "FStar.Extraction.ML.Modul.fst"
let def = (let _157_37 = (let _157_36 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _157_36 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _157_37 FStar_Syntax_Util.un_uinst))
in (
# 70 "FStar.Extraction.ML.Modul.fst"
let _73_42 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _73_35) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _73_39 -> begin
([], def)
end)
in (match (_73_42) with
| (bs, body) -> begin
(
# 73 "FStar.Extraction.ML.Modul.fst"
let _73_45 = (binders_as_mlty_binders env bs)
in (match (_73_45) with
| (env, ml_bs) -> begin
(
# 74 "FStar.Extraction.ML.Modul.fst"
let body = (let _157_38 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _157_38 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (
# 75 "FStar.Extraction.ML.Modul.fst"
let td = (((lident_as_mlsymbol lid), ml_bs, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body))))::[]
in (
# 76 "FStar.Extraction.ML.Modul.fst"
let def = (let _157_40 = (let _157_39 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_157_39))
in (_157_40)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (
# 77 "FStar.Extraction.ML.Modul.fst"
let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_1 -> (match (_73_1) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _73_53 -> begin
false
end)))) then begin
env
end else begin
(FStar_Extraction_ML_UEnv.extend_tydef env td)
end
in (env, def)))))
end))
end))))

# 86 "FStar.Extraction.ML.Modul.fst"
type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}

# 86 "FStar.Extraction.ML.Modul.fst"
let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))

# 91 "FStar.Extraction.ML.Modul.fst"
type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}

# 91 "FStar.Extraction.ML.Modul.fst"
let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))

# 99 "FStar.Extraction.ML.Modul.fst"
let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _157_75 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _157_74 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _157_73 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _157_72 = (let _157_71 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _157_70 = (let _157_68 = (FStar_Syntax_Print.lid_to_string d.dname)
in (Prims.strcat _157_68 " : "))
in (let _157_69 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat _157_70 _157_69))))))
in (FStar_All.pipe_right _157_71 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _157_75 _157_74 _157_73 _157_72))))))

# 106 "FStar.Extraction.ML.Modul.fst"
let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _73_3 -> (match (_73_3) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, _73_77, r) -> begin
(
# 110 "FStar.Extraction.ML.Modul.fst"
let _73_83 = (FStar_Syntax_Subst.open_term bs t)
in (match (_73_83) with
| (bs, t) -> begin
(
# 111 "FStar.Extraction.ML.Modul.fst"
let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _73_2 -> (match (_73_2) with
| FStar_Syntax_Syntax.Sig_datacon (d, _73_87, t, l', nparams, _73_92, _73_94, _73_96) when (FStar_Ident.lid_equals l l') -> begin
(
# 113 "FStar.Extraction.ML.Modul.fst"
let _73_101 = (FStar_Syntax_Util.arrow_formals t)
in (match (_73_101) with
| (bs', body) -> begin
(
# 114 "FStar.Extraction.ML.Modul.fst"
let _73_104 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_73_104) with
| (bs_params, rest) -> begin
(
# 115 "FStar.Extraction.ML.Modul.fst"
let subst = (FStar_List.map2 (fun _73_108 _73_112 -> (match ((_73_108, _73_112)) with
| ((b', _73_107), (b, _73_111)) -> begin
(let _157_84 = (let _157_83 = (FStar_Syntax_Syntax.bv_to_name b)
in (b', _157_83))
in FStar_Syntax_Syntax.NT (_157_84))
end)) bs_params bs)
in (
# 116 "FStar.Extraction.ML.Modul.fst"
let t = (let _157_86 = (let _157_85 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _157_85))
in (FStar_All.pipe_right _157_86 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _73_116 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _73_119 -> begin
[]
end)))))

# 127 "FStar.Extraction.ML.Modul.fst"
type env_t =
FStar_Extraction_ML_UEnv.env

# 129 "FStar.Extraction.ML.Modul.fst"
let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (
# 130 "FStar.Extraction.ML.Modul.fst"
let extract_ctor = (fun ml_tyvars env ctor -> (
# 131 "FStar.Extraction.ML.Modul.fst"
let mlt = (let _157_97 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _157_97))
in (
# 132 "FStar.Extraction.ML.Modul.fst"
let tys = (ml_tyvars, mlt)
in (
# 133 "FStar.Extraction.ML.Modul.fst"
let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _157_100 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _157_99 = (let _157_98 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((lident_as_mlsymbol ctor.dname), _157_98))
in (_157_100, _157_99)))))))
in (
# 137 "FStar.Extraction.ML.Modul.fst"
let extract_one_family = (fun env ind -> (
# 138 "FStar.Extraction.ML.Modul.fst"
let _73_134 = (binders_as_mlty_binders env ind.iparams)
in (match (_73_134) with
| (env, vars) -> begin
(
# 139 "FStar.Extraction.ML.Modul.fst"
let _73_137 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_73_137) with
| (env, ctors) -> begin
(
# 140 "FStar.Extraction.ML.Modul.fst"
let _73_141 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_73_141) with
| (indices, _73_140) -> begin
(
# 141 "FStar.Extraction.ML.Modul.fst"
let ml_params = (let _157_109 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _73_143 -> (let _157_108 = (let _157_107 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _157_107))
in (_157_108, 0)))))
in (FStar_List.append vars _157_109))
in (
# 142 "FStar.Extraction.ML.Modul.fst"
let tbody = (match ((FStar_Util.find_opt (fun _73_4 -> (match (_73_4) with
| FStar_Syntax_Syntax.RecordType (_73_148) -> begin
true
end
| _73_151 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(
# 144 "FStar.Extraction.ML.Modul.fst"
let _73_158 = (FStar_List.hd ctors)
in (match (_73_158) with
| (_73_156, c_ty) -> begin
(
# 145 "FStar.Extraction.ML.Modul.fst"
let _73_159 = ()
in (
# 146 "FStar.Extraction.ML.Modul.fst"
let fields = (FStar_List.map2 (fun lid ty -> ((lident_as_mlsymbol lid), ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _73_165 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in (env, ((lident_as_mlsymbol ind.iname), ml_params, Some (tbody)))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (FStar_Syntax_Syntax.Sig_datacon (l, _73_169, t, _73_172, _73_174, _73_176, _73_178, _73_180)::[], FStar_Syntax_Syntax.ExceptionConstructor::[], _73_187, r) -> begin
(
# 155 "FStar.Extraction.ML.Modul.fst"
let _73_193 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_73_193) with
| (env, ctor) -> begin
(env, (FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[])
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _73_197, r) -> begin
(
# 159 "FStar.Extraction.ML.Modul.fst"
let ifams = (bundle_as_inductive_families env ses quals)
in (
# 161 "FStar.Extraction.ML.Modul.fst"
let _73_204 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_73_204) with
| (env, td) -> begin
(env, (FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
end)))
end
| _73_206 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))

# 170 "FStar.Extraction.ML.Modul.fst"
let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (
# 171 "FStar.Extraction.ML.Modul.fst"
let l = (fun _73_5 -> (match (_73_5) with
| FStar_Extraction_ML_Term.Term_level -> begin
"Term_level"
end
| FStar_Extraction_ML_Term.Type_level -> begin
"Type_level"
end
| FStar_Extraction_ML_Term.Kind_level -> begin
"Kind_level"
end))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_Util.print_string "\t\tInductive bundle")
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_225, t, quals, _73_229) -> begin
(let _157_122 = (FStar_Syntax_Print.lid_to_string lid)
in (let _157_121 = (let _157_120 = (let _157_119 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _157_119))
in (l _157_120))
in (FStar_Util.print2 "\t\t%s @ %s" _157_122 _157_121)))
end
| FStar_Syntax_Syntax.Sig_let ((_73_233, lb::_73_235), _73_240, _73_242, _73_244) -> begin
(let _157_130 = (let _157_125 = (let _157_124 = (let _157_123 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _157_123.FStar_Syntax_Syntax.fv_name)
in _157_124.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _157_125 FStar_Syntax_Print.lid_to_string))
in (let _157_129 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _157_128 = (let _157_127 = (let _157_126 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _157_126))
in (l _157_127))
in (FStar_Util.print3 "\t\t%s : %s @ %s" _157_130 _157_129 _157_128))))
end
| _73_248 -> begin
(FStar_Util.print_string "other\n")
end)))

# 192 "FStar.Extraction.ML.Modul.fst"
let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (
# 193 "FStar.Extraction.ML.Modul.fst"
let _73_254 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (
# 194 "FStar.Extraction.ML.Modul.fst"
let _73_252 = (let _157_137 = (let _157_136 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _157_136))
in (FStar_Util.print_string _157_137))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_267, t, quals, _73_271) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _157_139 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_6 -> (match (_73_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _73_277 -> begin
false
end))))
in (FStar_All.pipe_right _157_139 Prims.op_Negation)) then begin
(g, [])
end else begin
(
# 205 "FStar.Extraction.ML.Modul.fst"
let _73_281 = (FStar_Syntax_Util.arrow_formals t)
in (match (_73_281) with
| (bs, _73_280) -> begin
(let _157_140 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g lid quals _157_140))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _73_287, _73_289, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _157_143 = (let _157_142 = (let _157_141 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _157_141.FStar_Syntax_Syntax.fv_name)
in _157_142.FStar_Syntax_Syntax.v)
in (extract_typ_abbrev g _157_143 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _73_296, quals) -> begin
(
# 212 "FStar.Extraction.ML.Modul.fst"
let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((lbs, FStar_Syntax_Const.exp_false_bool))) None r)
in (
# 213 "FStar.Extraction.ML.Modul.fst"
let _73_306 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_73_306) with
| (ml_let, _73_303, _73_305) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _73_309) -> begin
(
# 216 "FStar.Extraction.ML.Modul.fst"
let _73_341 = (FStar_List.fold_left2 (fun _73_314 ml_lb _73_324 -> (match ((_73_314, _73_324)) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _73_322; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _73_319; FStar_Syntax_Syntax.lbdef = _73_317}) -> begin
(
# 218 "FStar.Extraction.ML.Modul.fst"
let lb_lid = (let _157_148 = (let _157_147 = (FStar_Util.right lbname)
in _157_147.FStar_Syntax_Syntax.fv_name)
in _157_148.FStar_Syntax_Syntax.v)
in (
# 219 "FStar.Extraction.ML.Modul.fst"
let _73_338 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_7 -> (match (_73_7) with
| FStar_Syntax_Syntax.Projector (_73_328) -> begin
true
end
| _73_331 -> begin
false
end)))) then begin
(
# 221 "FStar.Extraction.ML.Modul.fst"
let mname = (let _157_150 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _157_150 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (
# 222 "FStar.Extraction.ML.Modul.fst"
let env = (let _157_152 = (FStar_Util.right lbname)
in (let _157_151 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _157_152 mname _157_151 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (env, (
# 223 "FStar.Extraction.ML.Modul.fst"
let _73_334 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _73_334.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _73_334.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _73_334.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _73_334.FStar_Extraction_ML_Syntax.print_typ}))))
end else begin
(let _157_155 = (let _157_154 = (let _157_153 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _157_153 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _157_154))
in (_157_155, ml_lb))
end
in (match (_73_338) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end)))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_73_341) with
| (g, ml_lbs') -> begin
(let _157_158 = (let _157_157 = (let _157_156 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_157_156))
in (_157_157)::(FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
in (g, _157_158))
end))
end
| _73_343 -> begin
(let _157_160 = (let _157_159 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _157_159))
in (FStar_All.failwith _157_160))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_346, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(
# 235 "FStar.Extraction.ML.Modul.fst"
let always_fail = (
# 236 "FStar.Extraction.ML.Modul.fst"
let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _157_161 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _157_161 None))
end)
in (let _157_167 = (let _157_166 = (let _157_165 = (let _157_164 = (let _157_163 = (let _157_162 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_157_162))
in {FStar_Syntax_Syntax.lbname = _157_163; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_157_164)::[])
in (false, _157_165))
in (_157_166, r, [], quals))
in FStar_Syntax_Syntax.Sig_let (_157_167)))
in (
# 244 "FStar.Extraction.ML.Modul.fst"
let _73_362 = (extract_sig g always_fail)
in (match (_73_362) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _73_8 -> (match (_73_8) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _73_367 -> begin
None
end)))) with
| Some (l) -> begin
(let _157_173 = (let _157_172 = (let _157_169 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_157_169))
in (let _157_171 = (let _157_170 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_157_170)::[])
in (_157_172)::_157_171))
in (g, _157_173))
end
| _73_371 -> begin
(match ((FStar_Util.find_map quals (fun _73_9 -> (match (_73_9) with
| FStar_Syntax_Syntax.Projector (l, _73_375) -> begin
Some (l)
end
| _73_379 -> begin
None
end)))) with
| Some (_73_381) -> begin
(g, [])
end
| _73_384 -> begin
(g, mlm)
end)
end)
end)))
end else begin
(g, [])
end
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 259 "FStar.Extraction.ML.Modul.fst"
let _73_394 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_73_394) with
| (ml_main, _73_391, _73_393) -> begin
(let _157_177 = (let _157_176 = (let _157_175 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_157_175))
in (_157_176)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in (g, _157_177))
end))
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

# 270 "FStar.Extraction.ML.Modul.fst"
let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _157_182 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _157_182 Prims.fst)))

# 272 "FStar.Extraction.ML.Modul.fst"
let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (
# 273 "FStar.Extraction.ML.Modul.fst"
let _73_414 = (FStar_Syntax_Syntax.reset_gensym ())
in (
# 274 "FStar.Extraction.ML.Modul.fst"
let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (
# 275 "FStar.Extraction.ML.Modul.fst"
let g = (
# 275 "FStar.Extraction.ML.Modul.fst"
let _73_417 = g
in {FStar_Extraction_ML_UEnv.tcenv = _73_417.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _73_417.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _73_417.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (let _157_187 = (FStar_ST.read FStar_Options.no_extract)
in (FStar_List.contains m.FStar_Syntax_Syntax.name.FStar_Ident.str _157_187))) then begin
(
# 279 "FStar.Extraction.ML.Modul.fst"
let g = (extract_iface g m)
in (g, []))
end else begin
(
# 281 "FStar.Extraction.ML.Modul.fst"
let _73_423 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_73_423) with
| (g, sigs) -> begin
(
# 282 "FStar.Extraction.ML.Modul.fst"
let mlm = (FStar_List.flatten sigs)
in (let _157_192 = (let _157_191 = (let _157_190 = (let _157_189 = (let _157_188 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_157_188, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_157_189)::[])
in FStar_Extraction_ML_Syntax.MLLib (_157_190))
in (_157_191)::[])
in (g, _157_192)))
end))
end))))




