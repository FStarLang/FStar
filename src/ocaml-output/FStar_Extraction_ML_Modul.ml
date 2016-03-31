
open Prims
# 37 "FStar.Extraction.ML.Modul.fst"
let fail_exp = (fun lid t -> (let _147_16 = (let _147_15 = (let _147_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _147_13 = (let _147_12 = (FStar_Syntax_Syntax.iarg t)
in (let _147_11 = (let _147_10 = (let _147_9 = (let _147_8 = (let _147_7 = (let _147_6 = (let _147_5 = (let _147_4 = (let _147_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _147_3))
in (FStar_Bytes.string_as_unicode_bytes _147_4))
in (_147_5, FStar_Range.dummyRange))
in FStar_Const.Const_string (_147_6))
in FStar_Syntax_Syntax.Tm_constant (_147_7))
in (FStar_Syntax_Syntax.mk _147_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _147_9))
in (_147_10)::[])
in (_147_12)::_147_11))
in (_147_14, _147_13)))
in FStar_Syntax_Syntax.Tm_app (_147_15))
in (FStar_Syntax_Syntax.mk _147_16 None FStar_Range.dummyRange)))

# 44 "FStar.Extraction.ML.Modul.fst"
let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (
# 45 "FStar.Extraction.ML.Modul.fst"
let projecteeName = x.FStar_Ident.ident
in (
# 46 "FStar.Extraction.ML.Modul.fst"
let _68_16 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_68_16) with
| (prefix, constrName) -> begin
(
# 47 "FStar.Extraction.ML.Modul.fst"
let mangledName = (FStar_Ident.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Ident.idText) "___") projecteeName.FStar_Ident.idText))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

# 50 "FStar.Extraction.ML.Modul.fst"
let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)

# 56 "FStar.Extraction.ML.Modul.fst"
let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _68_25 -> (match (_68_25) with
| (bv, _68_24) -> begin
(let _147_29 = (let _147_27 = (let _147_26 = (let _147_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_147_25))
in Some (_147_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _147_27))
in (let _147_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in (_147_29, _147_28)))
end)) env bs))

# 66 "FStar.Extraction.ML.Modul.fst"
let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env lid quals def -> (
# 67 "FStar.Extraction.ML.Modul.fst"
let def = (let _147_39 = (let _147_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _147_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _147_39 FStar_Syntax_Util.un_uinst))
in (
# 68 "FStar.Extraction.ML.Modul.fst"
let _68_41 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _68_34) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _68_38 -> begin
([], def)
end)
in (match (_68_41) with
| (bs, body) -> begin
(
# 71 "FStar.Extraction.ML.Modul.fst"
let _68_44 = (binders_as_mlty_binders env bs)
in (match (_68_44) with
| (env, ml_bs) -> begin
(
# 72 "FStar.Extraction.ML.Modul.fst"
let body = (let _147_40 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _147_40 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (
# 73 "FStar.Extraction.ML.Modul.fst"
let td = (((lident_as_mlsymbol lid), ml_bs, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body))))::[]
in (
# 74 "FStar.Extraction.ML.Modul.fst"
let def = (let _147_42 = (let _147_41 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_147_41))
in (_147_42)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (
# 75 "FStar.Extraction.ML.Modul.fst"
let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _68_1 -> (match (_68_1) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _68_52 -> begin
false
end)))) then begin
env
end else begin
(FStar_Extraction_ML_UEnv.extend_tydef env td)
end
in (env, def)))))
end))
end))))

# 84 "FStar.Extraction.ML.Modul.fst"
type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}

# 84 "FStar.Extraction.ML.Modul.fst"
let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))

# 89 "FStar.Extraction.ML.Modul.fst"
type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}

# 89 "FStar.Extraction.ML.Modul.fst"
let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))

# 97 "FStar.Extraction.ML.Modul.fst"
let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _147_77 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _147_76 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _147_75 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _147_74 = (let _147_73 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _147_72 = (let _147_70 = (FStar_Syntax_Print.lid_to_string d.dname)
in (Prims.strcat _147_70 " : "))
in (let _147_71 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat _147_72 _147_71))))))
in (FStar_All.pipe_right _147_73 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _147_77 _147_76 _147_75 _147_74))))))

# 104 "FStar.Extraction.ML.Modul.fst"
let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _68_3 -> (match (_68_3) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(
# 108 "FStar.Extraction.ML.Modul.fst"
let _68_81 = (FStar_Syntax_Subst.open_term bs t)
in (match (_68_81) with
| (bs, t) -> begin
(
# 109 "FStar.Extraction.ML.Modul.fst"
let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _68_2 -> (match (_68_2) with
| FStar_Syntax_Syntax.Sig_datacon (d, _68_85, t, l', nparams, _68_90, _68_92, _68_94) when (FStar_Ident.lid_equals l l') -> begin
(
# 111 "FStar.Extraction.ML.Modul.fst"
let _68_99 = (FStar_Syntax_Util.arrow_formals t)
in (match (_68_99) with
| (bs', body) -> begin
(
# 112 "FStar.Extraction.ML.Modul.fst"
let _68_102 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_68_102) with
| (bs_params, rest) -> begin
(
# 113 "FStar.Extraction.ML.Modul.fst"
let subst = (FStar_List.map2 (fun _68_106 _68_110 -> (match ((_68_106, _68_110)) with
| ((b', _68_105), (b, _68_109)) -> begin
(let _147_86 = (let _147_85 = (FStar_Syntax_Syntax.bv_to_name b)
in (b', _147_85))
in FStar_Syntax_Syntax.NT (_147_86))
end)) bs_params bs)
in (
# 114 "FStar.Extraction.ML.Modul.fst"
let t = (let _147_88 = (let _147_87 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _147_87))
in (FStar_All.pipe_right _147_88 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _68_114 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _68_117 -> begin
[]
end)))))

# 125 "FStar.Extraction.ML.Modul.fst"
type env_t =
FStar_Extraction_ML_UEnv.env

# 127 "FStar.Extraction.ML.Modul.fst"
let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (
# 128 "FStar.Extraction.ML.Modul.fst"
let extract_ctor = (fun ml_tyvars env ctor -> (
# 129 "FStar.Extraction.ML.Modul.fst"
let mlt = (let _147_99 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _147_99))
in (
# 130 "FStar.Extraction.ML.Modul.fst"
let tys = (ml_tyvars, mlt)
in (
# 131 "FStar.Extraction.ML.Modul.fst"
let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _147_102 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _147_101 = (let _147_100 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((lident_as_mlsymbol ctor.dname), _147_100))
in (_147_102, _147_101)))))))
in (
# 135 "FStar.Extraction.ML.Modul.fst"
let extract_one_family = (fun env ind -> (
# 136 "FStar.Extraction.ML.Modul.fst"
let _68_132 = (binders_as_mlty_binders env ind.iparams)
in (match (_68_132) with
| (env, vars) -> begin
(
# 137 "FStar.Extraction.ML.Modul.fst"
let _68_135 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_68_135) with
| (env, ctors) -> begin
(
# 138 "FStar.Extraction.ML.Modul.fst"
let _68_139 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_68_139) with
| (indices, _68_138) -> begin
(
# 139 "FStar.Extraction.ML.Modul.fst"
let ml_params = (let _147_111 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _68_141 -> (let _147_110 = (let _147_109 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _147_109))
in (_147_110, 0)))))
in (FStar_List.append vars _147_111))
in (
# 140 "FStar.Extraction.ML.Modul.fst"
let tbody = (match ((FStar_Util.find_opt (fun _68_4 -> (match (_68_4) with
| FStar_Syntax_Syntax.RecordType (_68_146) -> begin
true
end
| _68_149 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(
# 142 "FStar.Extraction.ML.Modul.fst"
let _68_156 = (FStar_List.hd ctors)
in (match (_68_156) with
| (_68_154, c_ty) -> begin
(
# 143 "FStar.Extraction.ML.Modul.fst"
let _68_157 = ()
in (
# 144 "FStar.Extraction.ML.Modul.fst"
let fields = (FStar_List.map2 (fun lid ty -> ((lident_as_mlsymbol lid), ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _68_163 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in (env, ((lident_as_mlsymbol ind.iname), ml_params, Some (tbody)))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (FStar_Syntax_Syntax.Sig_datacon (l, _68_167, t, _68_170, _68_172, _68_174, _68_176, _68_178)::[], FStar_Syntax_Syntax.ExceptionConstructor::[], _68_185, r) -> begin
(
# 153 "FStar.Extraction.ML.Modul.fst"
let _68_191 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_68_191) with
| (env, ctor) -> begin
(env, (FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[])
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _68_195, r) -> begin
(
# 157 "FStar.Extraction.ML.Modul.fst"
let ifams = (bundle_as_inductive_families env ses quals)
in (
# 159 "FStar.Extraction.ML.Modul.fst"
let _68_202 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_68_202) with
| (env, td) -> begin
(env, (FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
end)))
end
| _68_204 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))

# 168 "FStar.Extraction.ML.Modul.fst"
let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (
# 169 "FStar.Extraction.ML.Modul.fst"
let l = (fun _68_5 -> (match (_68_5) with
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
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _68_223, t, quals, _68_227) -> begin
(let _147_124 = (FStar_Syntax_Print.lid_to_string lid)
in (let _147_123 = (let _147_122 = (let _147_121 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _147_121))
in (l _147_122))
in (FStar_Util.print2 "\t\t%s @ %s\n" _147_124 _147_123)))
end
| FStar_Syntax_Syntax.Sig_let ((_68_231, lb::_68_233), _68_238, _68_240, _68_242) -> begin
(let _147_132 = (let _147_127 = (let _147_126 = (let _147_125 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _147_125.FStar_Syntax_Syntax.fv_name)
in _147_126.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _147_127 FStar_Syntax_Print.lid_to_string))
in (let _147_131 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_130 = (let _147_129 = (let _147_128 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _147_128))
in (l _147_129))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _147_132 _147_131 _147_130))))
end
| _68_246 -> begin
(FStar_Util.print_string "other\n")
end)))

# 190 "FStar.Extraction.ML.Modul.fst"
let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (
# 191 "FStar.Extraction.ML.Modul.fst"
let _68_252 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (
# 192 "FStar.Extraction.ML.Modul.fst"
let _68_250 = (let _147_139 = (let _147_138 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _147_138))
in (FStar_Util.print_string _147_139))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _68_265, t, quals, _68_269) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _147_141 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _68_6 -> (match (_68_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _68_275 -> begin
false
end))))
in (FStar_All.pipe_right _147_141 Prims.op_Negation)) then begin
(g, [])
end else begin
(
# 203 "FStar.Extraction.ML.Modul.fst"
let _68_279 = (FStar_Syntax_Util.arrow_formals t)
in (match (_68_279) with
| (bs, _68_278) -> begin
(let _147_142 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g lid quals _147_142))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _68_285, _68_287, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _147_145 = (let _147_144 = (let _147_143 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _147_143.FStar_Syntax_Syntax.fv_name)
in _147_144.FStar_Syntax_Syntax.v)
in (extract_typ_abbrev g _147_145 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _68_294, quals) -> begin
(
# 210 "FStar.Extraction.ML.Modul.fst"
let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((lbs, FStar_Syntax_Const.exp_false_bool))) None r)
in (
# 211 "FStar.Extraction.ML.Modul.fst"
let _68_304 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_68_304) with
| (ml_let, _68_301, _68_303) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _68_307) -> begin
(
# 214 "FStar.Extraction.ML.Modul.fst"
let _68_339 = (FStar_List.fold_left2 (fun _68_312 ml_lb _68_322 -> (match ((_68_312, _68_322)) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _68_320; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _68_317; FStar_Syntax_Syntax.lbdef = _68_315}) -> begin
(
# 216 "FStar.Extraction.ML.Modul.fst"
let lb_lid = (let _147_150 = (let _147_149 = (FStar_Util.right lbname)
in _147_149.FStar_Syntax_Syntax.fv_name)
in _147_150.FStar_Syntax_Syntax.v)
in (
# 217 "FStar.Extraction.ML.Modul.fst"
let _68_336 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _68_7 -> (match (_68_7) with
| FStar_Syntax_Syntax.Projector (_68_326) -> begin
true
end
| _68_329 -> begin
false
end)))) then begin
(
# 219 "FStar.Extraction.ML.Modul.fst"
let mname = (let _147_152 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _147_152 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (
# 220 "FStar.Extraction.ML.Modul.fst"
let env = (let _147_154 = (FStar_Util.right lbname)
in (let _147_153 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _147_154 mname _147_153 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (env, (
# 221 "FStar.Extraction.ML.Modul.fst"
let _68_332 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _68_332.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _68_332.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _68_332.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _68_332.FStar_Extraction_ML_Syntax.print_typ}))))
end else begin
(let _147_157 = (let _147_156 = (let _147_155 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _147_155 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _147_156))
in (_147_157, ml_lb))
end
in (match (_68_336) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end)))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_68_339) with
| (g, ml_lbs') -> begin
(let _147_160 = (let _147_159 = (let _147_158 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_147_158))
in (_147_159)::(FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
in (g, _147_160))
end))
end
| _68_341 -> begin
(let _147_162 = (let _147_161 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _147_161))
in (FStar_All.failwith _147_162))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _68_344, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(
# 233 "FStar.Extraction.ML.Modul.fst"
let always_fail = (
# 234 "FStar.Extraction.ML.Modul.fst"
let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _147_163 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _147_163 None))
end)
in (let _147_169 = (let _147_168 = (let _147_167 = (let _147_166 = (let _147_165 = (let _147_164 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_147_164))
in {FStar_Syntax_Syntax.lbname = _147_165; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_147_166)::[])
in (false, _147_167))
in (_147_168, r, [], quals))
in FStar_Syntax_Syntax.Sig_let (_147_169)))
in (
# 242 "FStar.Extraction.ML.Modul.fst"
let _68_360 = (extract_sig g always_fail)
in (match (_68_360) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _68_8 -> (match (_68_8) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _68_365 -> begin
None
end)))) with
| Some (l) -> begin
(let _147_175 = (let _147_174 = (let _147_171 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_147_171))
in (let _147_173 = (let _147_172 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_147_172)::[])
in (_147_174)::_147_173))
in (g, _147_175))
end
| _68_369 -> begin
(match ((FStar_Util.find_map quals (fun _68_9 -> (match (_68_9) with
| FStar_Syntax_Syntax.Projector (l, _68_373) -> begin
Some (l)
end
| _68_377 -> begin
None
end)))) with
| Some (_68_379) -> begin
(g, [])
end
| _68_382 -> begin
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
# 257 "FStar.Extraction.ML.Modul.fst"
let _68_392 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_68_392) with
| (ml_main, _68_389, _68_391) -> begin
(let _147_179 = (let _147_178 = (let _147_177 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_147_177))
in (_147_178)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in (g, _147_179))
end))
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

# 268 "FStar.Extraction.ML.Modul.fst"
let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _147_184 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _147_184 Prims.fst)))

# 270 "FStar.Extraction.ML.Modul.fst"
let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (
# 271 "FStar.Extraction.ML.Modul.fst"
let _68_412 = (FStar_Syntax_Syntax.reset_gensym ())
in (
# 272 "FStar.Extraction.ML.Modul.fst"
let _68_414 = (let _147_189 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _147_189))
in (
# 273 "FStar.Extraction.ML.Modul.fst"
let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (
# 274 "FStar.Extraction.ML.Modul.fst"
let g = (
# 274 "FStar.Extraction.ML.Modul.fst"
let _68_417 = g
in {FStar_Extraction_ML_UEnv.tcenv = _68_417.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _68_417.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _68_417.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (let _147_190 = (FStar_ST.read FStar_Options.no_extract)
in (FStar_List.contains m.FStar_Syntax_Syntax.name.FStar_Ident.str _147_190))) then begin
(
# 278 "FStar.Extraction.ML.Modul.fst"
let g = (extract_iface g m)
in (g, []))
end else begin
(
# 280 "FStar.Extraction.ML.Modul.fst"
let _68_423 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_68_423) with
| (g, sigs) -> begin
(
# 281 "FStar.Extraction.ML.Modul.fst"
let mlm = (FStar_List.flatten sigs)
in (let _147_195 = (let _147_194 = (let _147_193 = (let _147_192 = (let _147_191 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_147_191, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_147_192)::[])
in FStar_Extraction_ML_Syntax.MLLib (_147_193))
in (_147_194)::[])
in (g, _147_195)))
end))
end)))))




