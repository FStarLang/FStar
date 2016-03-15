
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
let _73_14 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_73_14) with
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
let binders_as_mlty_binders = (fun g bs -> (
# 59 "FStar.Extraction.ML.Modul.fst"
let _73_29 = (FStar_List.fold_left (fun _73_22 _73_26 -> (match ((_73_22, _73_26)) with
| ((env, bs), (bv, _73_25)) -> begin
if (FStar_Extraction_ML_Term.is_type bv.FStar_Syntax_Syntax.sort) then begin
(let _157_27 = (FStar_Extraction_ML_UEnv.extend_ty g bv (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((bv_as_ml_tyvar bv)))))
in (_157_27, ((bv_as_ml_tyvar bv))::bs))
end else begin
(let _157_28 = (FStar_Extraction_ML_UEnv.extend_bv g bv ([], FStar_Extraction_ML_UEnv.erasedContent) false false false)
in (_157_28, ((bv_as_ml_tyvar bv))::bs))
end
end)) (g, []) bs)
in (match (_73_29) with
| (g, bs) -> begin
((FStar_List.rev bs), g)
end)))

# 67 "FStar.Extraction.ML.Modul.fst"
let extract_typ_abbrev = (fun env lid quals def -> (
# 68 "FStar.Extraction.ML.Modul.fst"
let def = (let _157_34 = (let _157_33 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _157_33 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _157_34 FStar_Syntax_Util.un_uinst))
in (
# 69 "FStar.Extraction.ML.Modul.fst"
let _73_45 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _73_38) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _73_42 -> begin
([], def)
end)
in (match (_73_45) with
| (bs, body) -> begin
(
# 72 "FStar.Extraction.ML.Modul.fst"
let _73_48 = (binders_as_mlty_binders env bs)
in (match (_73_48) with
| (ml_bs, env) -> begin
(
# 73 "FStar.Extraction.ML.Modul.fst"
let body = (let _157_35 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _157_35 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (
# 74 "FStar.Extraction.ML.Modul.fst"
let td = (((lident_as_mlsymbol lid), ml_bs, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body))))::[]
in (
# 75 "FStar.Extraction.ML.Modul.fst"
let def = (let _157_37 = (let _157_36 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_157_36))
in (_157_37)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (
# 76 "FStar.Extraction.ML.Modul.fst"
let env = (FStar_Extraction_ML_UEnv.extend_tydef env td)
in (env, def)))))
end))
end))))

# 83 "FStar.Extraction.ML.Modul.fst"
type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}

# 83 "FStar.Extraction.ML.Modul.fst"
let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))

# 88 "FStar.Extraction.ML.Modul.fst"
type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}

# 88 "FStar.Extraction.ML.Modul.fst"
let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))

# 97 "FStar.Extraction.ML.Modul.fst"
let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _73_2 -> (match (_73_2) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, _73_73, r) -> begin
(
# 101 "FStar.Extraction.ML.Modul.fst"
let _73_79 = (FStar_Syntax_Subst.open_term bs t)
in (match (_73_79) with
| (bs, t) -> begin
(
# 102 "FStar.Extraction.ML.Modul.fst"
let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _73_1 -> (match (_73_1) with
| FStar_Syntax_Syntax.Sig_datacon (d, _73_83, t, l', nparams, _73_88, _73_90, _73_92) when (FStar_Ident.lid_equals l l') -> begin
(
# 104 "FStar.Extraction.ML.Modul.fst"
let _73_97 = (FStar_Syntax_Util.arrow_formals t)
in (match (_73_97) with
| (bs', body) -> begin
(
# 105 "FStar.Extraction.ML.Modul.fst"
let _73_100 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_73_100) with
| (bs_params, rest) -> begin
(
# 106 "FStar.Extraction.ML.Modul.fst"
let subst = (FStar_List.map2 (fun _73_104 _73_108 -> (match ((_73_104, _73_108)) with
| ((b', _73_103), (b, _73_107)) -> begin
(let _157_69 = (let _157_68 = (FStar_Syntax_Syntax.bv_to_tm b)
in (b', _157_68))
in FStar_Syntax_Syntax.NT (_157_69))
end)) bs_params bs)
in (
# 107 "FStar.Extraction.ML.Modul.fst"
let t = (let _157_70 = (FStar_Syntax_Util.abs rest body None)
in (FStar_All.pipe_right _157_70 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _73_112 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _73_115 -> begin
[]
end)))))

# 118 "FStar.Extraction.ML.Modul.fst"
type env_t =
FStar_Extraction_ML_UEnv.env

# 120 "FStar.Extraction.ML.Modul.fst"
let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (
# 121 "FStar.Extraction.ML.Modul.fst"
let extract_ctor = (fun ml_tyvars c ctor -> (
# 122 "FStar.Extraction.ML.Modul.fst"
let mlt = (let _157_81 = (FStar_Extraction_ML_Term.term_as_mlty c ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold c) _157_81))
in (
# 123 "FStar.Extraction.ML.Modul.fst"
let tys = (ml_tyvars, mlt)
in (
# 124 "FStar.Extraction.ML.Modul.fst"
let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _157_84 = (FStar_Extraction_ML_UEnv.extend_fv c fvv tys false false)
in (let _157_83 = (let _157_82 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((lident_as_mlsymbol ctor.dname), _157_82))
in (_157_84, _157_83)))))))
in (
# 131 "FStar.Extraction.ML.Modul.fst"
let extract_one_family = (fun env ind -> (
# 132 "FStar.Extraction.ML.Modul.fst"
let _73_130 = (binders_as_mlty_binders env ind.iparams)
in (match (_73_130) with
| (vars, env) -> begin
(
# 133 "FStar.Extraction.ML.Modul.fst"
let _73_133 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_73_133) with
| (env, ctors) -> begin
(
# 134 "FStar.Extraction.ML.Modul.fst"
let _73_137 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_73_137) with
| (indices, _73_136) -> begin
(
# 135 "FStar.Extraction.ML.Modul.fst"
let ml_params = (let _157_93 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _73_139 -> (let _157_92 = (let _157_91 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _157_91))
in (_157_92, 0)))))
in (FStar_List.append vars _157_93))
in (
# 136 "FStar.Extraction.ML.Modul.fst"
let tbody = (match ((FStar_Util.find_opt (fun _73_3 -> (match (_73_3) with
| FStar_Syntax_Syntax.RecordType (_73_144) -> begin
true
end
| _73_147 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(
# 138 "FStar.Extraction.ML.Modul.fst"
let _73_154 = (FStar_List.hd ctors)
in (match (_73_154) with
| (_73_152, c_ty) -> begin
(
# 139 "FStar.Extraction.ML.Modul.fst"
let _73_155 = ()
in (
# 140 "FStar.Extraction.ML.Modul.fst"
let fields = (FStar_List.map2 (fun lid ty -> ((lident_as_mlsymbol lid), ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _73_161 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in (env, ((lident_as_mlsymbol ind.iname), ml_params, Some (tbody)))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (FStar_Syntax_Syntax.Sig_datacon (l, _73_165, t, _73_168, _73_170, _73_172, _73_174, _73_176)::[], FStar_Syntax_Syntax.ExceptionConstructor::[], _73_183, r) -> begin
(
# 149 "FStar.Extraction.ML.Modul.fst"
let _73_189 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_73_189) with
| (env, ctor) -> begin
(env, (FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[])
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _73_193, r) -> begin
(
# 153 "FStar.Extraction.ML.Modul.fst"
let ifams = (bundle_as_inductive_families env ses quals)
in (
# 154 "FStar.Extraction.ML.Modul.fst"
let _73_200 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_73_200) with
| (env, td) -> begin
(env, (FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
end)))
end
| _73_202 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))

# 163 "FStar.Extraction.ML.Modul.fst"
let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (
# 164 "FStar.Extraction.ML.Modul.fst"
let _73_206 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _157_103 = (let _157_102 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _157_102))
in (FStar_Util.print_string _157_103))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_219, t, quals, _73_223) when ((FStar_Extraction_ML_Term.level t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _157_105 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_4 -> (match (_73_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _73_229 -> begin
false
end))))
in (FStar_All.pipe_right _157_105 Prims.op_Negation)) then begin
(g, [])
end else begin
(
# 174 "FStar.Extraction.ML.Modul.fst"
let _73_233 = (FStar_Syntax_Util.arrow_formals t)
in (match (_73_233) with
| (bs, _73_232) -> begin
(let _157_106 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g lid quals _157_106))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _73_239, quals, _73_242) when (FStar_Extraction_ML_Term.is_type lb.FStar_Syntax_Syntax.lbtyp) -> begin
(let _157_109 = (let _157_108 = (let _157_107 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _157_107.FStar_Syntax_Syntax.fv_name)
in _157_108.FStar_Syntax_Syntax.v)
in (extract_typ_abbrev g _157_109 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _73_248, quals) -> begin
(
# 181 "FStar.Extraction.ML.Modul.fst"
let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((lbs, FStar_Syntax_Const.exp_false_bool))) None r)
in (
# 182 "FStar.Extraction.ML.Modul.fst"
let _73_258 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_73_258) with
| (ml_let, _73_255, _73_257) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _73_261) -> begin
(
# 185 "FStar.Extraction.ML.Modul.fst"
let _73_293 = (FStar_List.fold_left2 (fun _73_266 ml_lb _73_276 -> (match ((_73_266, _73_276)) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _73_274; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _73_271; FStar_Syntax_Syntax.lbdef = _73_269}) -> begin
(
# 187 "FStar.Extraction.ML.Modul.fst"
let lb_lid = (let _157_114 = (let _157_113 = (FStar_Util.right lbname)
in _157_113.FStar_Syntax_Syntax.fv_name)
in _157_114.FStar_Syntax_Syntax.v)
in (
# 188 "FStar.Extraction.ML.Modul.fst"
let _73_290 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_5 -> (match (_73_5) with
| FStar_Syntax_Syntax.Projector (_73_280) -> begin
true
end
| _73_283 -> begin
false
end)))) then begin
(
# 190 "FStar.Extraction.ML.Modul.fst"
let mname = (let _157_116 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _157_116 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (
# 191 "FStar.Extraction.ML.Modul.fst"
let env = (let _157_118 = (FStar_Util.right lbname)
in (let _157_117 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _157_118 mname _157_117 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (env, (
# 192 "FStar.Extraction.ML.Modul.fst"
let _73_286 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _73_286.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _73_286.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _73_286.FStar_Extraction_ML_Syntax.mllb_def}))))
end else begin
(let _157_121 = (let _157_120 = (let _157_119 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _157_119 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _157_120))
in (_157_121, ml_lb))
end
in (match (_73_290) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end)))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_73_293) with
| (g, ml_lbs') -> begin
(let _157_124 = (let _157_123 = (let _157_122 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_157_122))
in (_157_123)::(FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
in (g, _157_124))
end))
end
| _73_295 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_298, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(
# 205 "FStar.Extraction.ML.Modul.fst"
let _73_306 = (FStar_Syntax_Util.arrow_formals t)
in (match (_73_306) with
| (bs, t) -> begin
(
# 206 "FStar.Extraction.ML.Modul.fst"
let imp = (match (bs) with
| [] -> begin
(fail_exp lid t)
end
| _73_309 -> begin
(let _157_125 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _157_125 None))
end)
in (
# 209 "FStar.Extraction.ML.Modul.fst"
let se = (let _157_131 = (let _157_130 = (let _157_129 = (let _157_128 = (let _157_127 = (let _157_126 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_157_126))
in {FStar_Syntax_Syntax.lbname = _157_127; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_157_128)::[])
in (false, _157_129))
in (_157_130, r, [], quals))
in FStar_Syntax_Syntax.Sig_let (_157_131))
in (
# 214 "FStar.Extraction.ML.Modul.fst"
let _73_314 = (extract_sig g se)
in (match (_73_314) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _73_6 -> (match (_73_6) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _73_319 -> begin
None
end)))) with
| Some (l) -> begin
(let _157_137 = (let _157_136 = (let _157_133 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_157_133))
in (let _157_135 = (let _157_134 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_157_134)::[])
in (_157_136)::_157_135))
in (g, _157_137))
end
| _73_323 -> begin
(match ((FStar_Util.find_map quals (fun _73_7 -> (match (_73_7) with
| FStar_Syntax_Syntax.Projector (l, _73_327) -> begin
Some (l)
end
| _73_331 -> begin
None
end)))) with
| Some (_73_333) -> begin
(g, [])
end
| _73_336 -> begin
(g, mlm)
end)
end)
end))))
end))
end else begin
(g, [])
end
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 225 "FStar.Extraction.ML.Modul.fst"
let _73_346 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_73_346) with
| (ml_main, _73_343, _73_345) -> begin
(let _157_141 = (let _157_140 = (let _157_139 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_157_139))
in (_157_140)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in (g, _157_141))
end))
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

# 236 "FStar.Extraction.ML.Modul.fst"
let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _157_146 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _157_146 Prims.fst)))

# 238 "FStar.Extraction.ML.Modul.fst"
let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (
# 239 "FStar.Extraction.ML.Modul.fst"
let _73_366 = (FStar_Syntax_Syntax.reset_gensym ())
in (
# 240 "FStar.Extraction.ML.Modul.fst"
let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (
# 241 "FStar.Extraction.ML.Modul.fst"
let g = (
# 241 "FStar.Extraction.ML.Modul.fst"
let _73_369 = g
in {FStar_Extraction_ML_UEnv.tcenv = _73_369.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _73_369.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _73_369.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (let _157_151 = (FStar_ST.read FStar_Options.no_extract)
in (FStar_List.contains m.FStar_Syntax_Syntax.name.FStar_Ident.str _157_151))) then begin
(
# 245 "FStar.Extraction.ML.Modul.fst"
let g = (extract_iface g m)
in (g, []))
end else begin
(
# 247 "FStar.Extraction.ML.Modul.fst"
let _73_375 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_73_375) with
| (g, sigs) -> begin
(
# 248 "FStar.Extraction.ML.Modul.fst"
let mlm = (FStar_List.flatten sigs)
in (let _157_156 = (let _157_155 = (let _157_154 = (let _157_153 = (let _157_152 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_157_152, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_157_153)::[])
in FStar_Extraction_ML_Syntax.MLLib (_157_154))
in (_157_155)::[])
in (g, _157_156)))
end))
end))))




