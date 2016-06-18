
open Prims

let fail_exp = (fun lid t -> (let _169_16 = (let _169_15 = (let _169_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _169_13 = (let _169_12 = (FStar_Syntax_Syntax.iarg t)
in (let _169_11 = (let _169_10 = (let _169_9 = (let _169_8 = (let _169_7 = (let _169_6 = (let _169_5 = (let _169_4 = (let _169_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _169_3))
in (FStar_Bytes.string_as_unicode_bytes _169_4))
in (_169_5, FStar_Range.dummyRange))
in FStar_Const.Const_string (_169_6))
in FStar_Syntax_Syntax.Tm_constant (_169_7))
in (FStar_Syntax_Syntax.mk _169_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _169_9))
in (_169_10)::[])
in (_169_12)::_169_11))
in (_169_14, _169_13)))
in FStar_Syntax_Syntax.Tm_app (_169_15))
in (FStar_Syntax_Syntax.mk _169_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _78_16 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_78_16) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Ident.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Ident.idText) "___") projecteeName.FStar_Ident.idText))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _78_25 -> (match (_78_25) with
| (bv, _78_24) -> begin
(let _169_29 = (let _169_27 = (let _169_26 = (let _169_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_169_25))
in Some (_169_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _169_27))
in (let _169_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in (_169_29, _169_28)))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env lid quals def -> (

let def = (let _169_39 = (let _169_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _169_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _169_39 FStar_Syntax_Util.un_uinst))
in (

let _78_41 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _78_34) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _78_38 -> begin
([], def)
end)
in (match (_78_41) with
| (bs, body) -> begin
(

let _78_44 = (binders_as_mlty_binders env bs)
in (match (_78_44) with
| (env, ml_bs) -> begin
(

let body = (let _169_40 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _169_40 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let td = (((lident_as_mlsymbol lid), ml_bs, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body))))::[]
in (

let def = (let _169_42 = (let _169_41 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_169_41))
in (_169_42)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_1 -> (match (_78_1) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _78_52 -> begin
false
end)))) then begin
env
end else begin
(FStar_Extraction_ML_UEnv.extend_tydef env td)
end
in (env, def)))))
end))
end))))


type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}


let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))


type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}


let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _169_77 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _169_76 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _169_75 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _169_74 = (let _169_73 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _169_72 = (let _169_70 = (FStar_Syntax_Print.lid_to_string d.dname)
in (Prims.strcat _169_70 " : "))
in (let _169_71 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat _169_72 _169_71))))))
in (FStar_All.pipe_right _169_73 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _169_77 _169_76 _169_75 _169_74))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _78_3 -> (match (_78_3) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _78_81 = (FStar_Syntax_Subst.open_term bs t)
in (match (_78_81) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _78_2 -> (match (_78_2) with
| FStar_Syntax_Syntax.Sig_datacon (d, _78_85, t, l', nparams, _78_90, _78_92, _78_94) when (FStar_Ident.lid_equals l l') -> begin
(

let _78_99 = (FStar_Syntax_Util.arrow_formals t)
in (match (_78_99) with
| (bs', body) -> begin
(

let _78_102 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_78_102) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _78_106 _78_110 -> (match ((_78_106, _78_110)) with
| ((b', _78_105), (b, _78_109)) -> begin
(let _169_86 = (let _169_85 = (FStar_Syntax_Syntax.bv_to_name b)
in (b', _169_85))
in FStar_Syntax_Syntax.NT (_169_86))
end)) bs_params bs)
in (

let t = (let _169_88 = (let _169_87 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _169_87))
in (FStar_All.pipe_right _169_88 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _78_114 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _78_117 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _169_99 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _169_99))
in (

let tys = (ml_tyvars, mlt)
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _169_102 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _169_101 = (let _169_100 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((lident_as_mlsymbol ctor.dname), _169_100))
in (_169_102, _169_101)))))))
in (

let extract_one_family = (fun env ind -> (

let _78_132 = (binders_as_mlty_binders env ind.iparams)
in (match (_78_132) with
| (env, vars) -> begin
(

let _78_135 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_78_135) with
| (env, ctors) -> begin
(

let _78_139 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_78_139) with
| (indices, _78_138) -> begin
(

let ml_params = (let _169_111 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _78_141 -> (let _169_110 = (let _169_109 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _169_109))
in (_169_110, 0)))))
in (FStar_List.append vars _169_111))
in (

let tbody = (match ((FStar_Util.find_opt (fun _78_4 -> (match (_78_4) with
| FStar_Syntax_Syntax.RecordType (_78_146) -> begin
true
end
| _78_149 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(

let _78_156 = (FStar_List.hd ctors)
in (match (_78_156) with
| (_78_154, c_ty) -> begin
(

let _78_157 = ()
in (

let fields = (FStar_List.map2 (fun lid ty -> ((lident_as_mlsymbol lid), ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _78_163 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in (env, ((lident_as_mlsymbol ind.iname), ml_params, Some (tbody)))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _78_167, t, _78_170, _78_172, _78_174, _78_176, _78_178))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _78_185, r) -> begin
(

let _78_191 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_78_191) with
| (env, ctor) -> begin
(env, (FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[])
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _78_195, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _78_202 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_78_202) with
| (env, td) -> begin
(env, (FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
end)))
end
| _78_204 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))


let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (

let l = (fun _78_5 -> (match (_78_5) with
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
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _78_223, t, quals, _78_227) -> begin
(let _169_124 = (FStar_Syntax_Print.lid_to_string lid)
in (let _169_123 = (let _169_122 = (let _169_121 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _169_121))
in (l _169_122))
in (FStar_Util.print2 "\t\t%s @ %s\n" _169_124 _169_123)))
end
| FStar_Syntax_Syntax.Sig_let ((_78_231, (lb)::_78_233), _78_238, _78_240, _78_242) -> begin
(let _169_132 = (let _169_127 = (let _169_126 = (let _169_125 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _169_125.FStar_Syntax_Syntax.fv_name)
in _169_126.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _169_127 FStar_Syntax_Print.lid_to_string))
in (let _169_131 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _169_130 = (let _169_129 = (let _169_128 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _169_128))
in (l _169_129))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _169_132 _169_131 _169_130))))
end
| _78_246 -> begin
(FStar_Util.print_string "other\n")
end)))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _78_252 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (

let _78_250 = (let _169_139 = (let _169_138 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _169_138))
in (FStar_Util.print_string _169_139))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _78_265, t, quals, _78_269) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _169_141 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_6 -> (match (_78_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _78_275 -> begin
false
end))))
in (FStar_All.pipe_right _169_141 Prims.op_Negation)) then begin
(g, [])
end else begin
(

let _78_279 = (FStar_Syntax_Util.arrow_formals t)
in (match (_78_279) with
| (bs, _78_278) -> begin
(let _169_142 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g lid quals _169_142))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _78_285, _78_287, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _169_145 = (let _169_144 = (let _169_143 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _169_143.FStar_Syntax_Syntax.fv_name)
in _169_144.FStar_Syntax_Syntax.v)
in (extract_typ_abbrev g _169_145 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _78_294, quals) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((lbs, FStar_Syntax_Const.exp_false_bool))) None r)
in (

let _78_304 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_78_304) with
| (ml_let, _78_301, _78_303) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _78_307) -> begin
(

let _78_339 = (FStar_List.fold_left2 (fun _78_312 ml_lb _78_322 -> (match ((_78_312, _78_322)) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _78_320; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _78_317; FStar_Syntax_Syntax.lbdef = _78_315}) -> begin
(

let lb_lid = (let _169_150 = (let _169_149 = (FStar_Util.right lbname)
in _169_149.FStar_Syntax_Syntax.fv_name)
in _169_150.FStar_Syntax_Syntax.v)
in (

let _78_336 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_7 -> (match (_78_7) with
| FStar_Syntax_Syntax.Projector (_78_326) -> begin
true
end
| _78_329 -> begin
false
end)))) then begin
(

let mname = (let _169_152 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _169_152 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _169_154 = (FStar_Util.right lbname)
in (let _169_153 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _169_154 mname _169_153 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (env, (

let _78_332 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _78_332.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _78_332.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _78_332.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _78_332.FStar_Extraction_ML_Syntax.print_typ}))))
end else begin
(let _169_157 = (let _169_156 = (let _169_155 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _169_155 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _169_156))
in (_169_157, ml_lb))
end
in (match (_78_336) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end)))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_78_339) with
| (g, ml_lbs') -> begin
(let _169_160 = (let _169_159 = (let _169_158 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_169_158))
in (_169_159)::(FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
in (g, _169_160))
end))
end
| _78_341 -> begin
(let _169_162 = (let _169_161 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _169_161))
in (FStar_All.failwith _169_162))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _78_344, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _169_163 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _169_163 None))
end)
in (let _169_169 = (let _169_168 = (let _169_167 = (let _169_166 = (let _169_165 = (let _169_164 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_169_164))
in {FStar_Syntax_Syntax.lbname = _169_165; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_169_166)::[])
in (false, _169_167))
in (_169_168, r, [], quals))
in FStar_Syntax_Syntax.Sig_let (_169_169)))
in (

let _78_360 = (extract_sig g always_fail)
in (match (_78_360) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _78_8 -> (match (_78_8) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _78_365 -> begin
None
end)))) with
| Some (l) -> begin
(let _169_175 = (let _169_174 = (let _169_171 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_169_171))
in (let _169_173 = (let _169_172 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_169_172)::[])
in (_169_174)::_169_173))
in (g, _169_175))
end
| _78_369 -> begin
(match ((FStar_Util.find_map quals (fun _78_9 -> (match (_78_9) with
| FStar_Syntax_Syntax.Projector (l, _78_373) -> begin
Some (l)
end
| _78_377 -> begin
None
end)))) with
| Some (_78_379) -> begin
(g, [])
end
| _78_382 -> begin
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

let _78_392 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_78_392) with
| (ml_main, _78_389, _78_391) -> begin
(let _169_179 = (let _169_178 = (let _169_177 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_169_177))
in (_169_178)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in (g, _169_179))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_78_394) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _169_184 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _169_184 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _78_415 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _78_418 = g
in {FStar_Extraction_ML_UEnv.tcenv = _78_418.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _78_418.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _78_418.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in (g, []))
end else begin
(

let _78_422 = (let _169_189 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _169_189))
in (

let _78_426 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_78_426) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (let _169_194 = (let _169_193 = (let _169_192 = (let _169_191 = (let _169_190 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_169_190, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_169_191)::[])
in FStar_Extraction_ML_Syntax.MLLib (_169_192))
in (_169_193)::[])
in (g, _169_194)))
end)))
end))))




