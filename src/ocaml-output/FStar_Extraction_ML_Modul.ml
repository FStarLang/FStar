
open Prims

let fail_exp = (fun lid t -> (let _172_16 = (let _172_15 = (let _172_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _172_13 = (let _172_12 = (FStar_Syntax_Syntax.iarg t)
in (let _172_11 = (let _172_10 = (let _172_9 = (let _172_8 = (let _172_7 = (let _172_6 = (let _172_5 = (let _172_4 = (let _172_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _172_3))
in (FStar_Bytes.string_as_unicode_bytes _172_4))
in ((_172_5), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (_172_6))
in FStar_Syntax_Syntax.Tm_constant (_172_7))
in (FStar_Syntax_Syntax.mk _172_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _172_9))
in (_172_10)::[])
in (_172_12)::_172_11))
in ((_172_14), (_172_13))))
in FStar_Syntax_Syntax.Tm_app (_172_15))
in (FStar_Syntax_Syntax.mk _172_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _79_17 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_79_17) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Ident.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _79_26 -> (match (_79_26) with
| (bv, _79_25) -> begin
(let _172_29 = (let _172_27 = (let _172_26 = (let _172_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_172_25))
in Some (_172_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _172_27))
in (let _172_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_172_29), (_172_28))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env lid quals def -> (

let def = (let _172_39 = (let _172_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _172_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _172_39 FStar_Syntax_Util.un_uinst))
in (

let _79_42 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _79_35) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _79_39 -> begin
(([]), (def))
end)
in (match (_79_42) with
| (bs, body) -> begin
(

let _79_45 = (binders_as_mlty_binders env bs)
in (match (_79_45) with
| (env, ml_bs) -> begin
(

let body = (let _172_40 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _172_40 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let td = ((((lident_as_mlsymbol lid)), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body)))))::[]
in (

let def = (let _172_42 = (let _172_41 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_172_41))
in (_172_42)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_1 -> (match (_79_1) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _79_53 -> begin
false
end)))) then begin
env
end else begin
(FStar_Extraction_ML_UEnv.extend_tydef env td)
end
in ((env), (def))))))
end))
end))))


type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}


let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))


type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}


let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _172_77 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _172_76 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _172_75 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _172_74 = (let _172_73 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _172_72 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _172_71 = (let _172_70 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _172_70))
in (Prims.strcat _172_72 _172_71))))))
in (FStar_All.pipe_right _172_73 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _172_77 _172_76 _172_75 _172_74))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _79_3 -> (match (_79_3) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _79_82 = (FStar_Syntax_Subst.open_term bs t)
in (match (_79_82) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _79_2 -> (match (_79_2) with
| FStar_Syntax_Syntax.Sig_datacon (d, _79_86, t, l', nparams, _79_91, _79_93, _79_95) when (FStar_Ident.lid_equals l l') -> begin
(

let _79_100 = (FStar_Syntax_Util.arrow_formals t)
in (match (_79_100) with
| (bs', body) -> begin
(

let _79_103 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_79_103) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _79_107 _79_111 -> (match (((_79_107), (_79_111))) with
| ((b', _79_106), (b, _79_110)) -> begin
(let _172_86 = (let _172_85 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_172_85)))
in FStar_Syntax_Syntax.NT (_172_86))
end)) bs_params bs)
in (

let t = (let _172_88 = (let _172_87 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _172_87))
in (FStar_All.pipe_right _172_88 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _79_115 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _79_118 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _172_99 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _172_99))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _172_102 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _172_101 = (let _172_100 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_172_100)))
in ((_172_102), (_172_101))))))))
in (

let extract_one_family = (fun env ind -> (

let _79_133 = (binders_as_mlty_binders env ind.iparams)
in (match (_79_133) with
| (env, vars) -> begin
(

let _79_136 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_79_136) with
| (env, ctors) -> begin
(

let _79_140 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_79_140) with
| (indices, _79_139) -> begin
(

let ml_params = (let _172_111 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _79_142 -> (let _172_110 = (let _172_109 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _172_109))
in ((_172_110), (0))))))
in (FStar_List.append vars _172_111))
in (

let tbody = (match ((FStar_Util.find_opt (fun _79_4 -> (match (_79_4) with
| FStar_Syntax_Syntax.RecordType (_79_147) -> begin
true
end
| _79_150 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(

let _79_157 = (FStar_List.hd ctors)
in (match (_79_157) with
| (_79_155, c_ty) -> begin
(

let _79_158 = ()
in (

let fields = (FStar_List.map2 (fun lid ty -> (((lident_as_mlsymbol lid)), (ty))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _79_164 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in ((env), ((((lident_as_mlsymbol ind.iname)), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _79_168, t, _79_171, _79_173, _79_175, _79_177, _79_179))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _79_186, r) -> begin
(

let _79_192 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_79_192) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _79_196, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _79_203 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_79_203) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _79_205 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))


let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (

let l = (fun _79_5 -> (match (_79_5) with
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
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _79_224, t, quals, _79_228) -> begin
(let _172_124 = (FStar_Syntax_Print.lid_to_string lid)
in (let _172_123 = (let _172_122 = (let _172_121 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _172_121))
in (l _172_122))
in (FStar_Util.print2 "\t\t%s @ %s\n" _172_124 _172_123)))
end
| FStar_Syntax_Syntax.Sig_let ((_79_232, (lb)::_79_234), _79_239, _79_241, _79_243) -> begin
(let _172_132 = (let _172_127 = (let _172_126 = (let _172_125 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _172_125.FStar_Syntax_Syntax.fv_name)
in _172_126.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_127 FStar_Syntax_Print.lid_to_string))
in (let _172_131 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _172_130 = (let _172_129 = (let _172_128 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _172_128))
in (l _172_129))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _172_132 _172_131 _172_130))))
end
| _79_247 -> begin
(FStar_Util.print_string "other\n")
end)))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _79_253 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (

let _79_251 = (let _172_139 = (let _172_138 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _172_138))
in (FStar_Util.print_string _172_139))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _79_266) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _172_150 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _172_150 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), (0)); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NoLetQualifier), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (match ((let _172_153 = (FStar_Syntax_Subst.compress tm)
in _172_153.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _79_282) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let _79_293 = (let _172_154 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _172_154))
in (match (_79_293) with
| (_79_289, tysc, _79_292) -> begin
(let _172_155 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_172_155), (tysc)))
end)))
end
| _79_295 -> begin
(FStar_All.failwith "Not an fv")
end))
in (

let extract_action = (fun g a -> (

let _79_301 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_79_301) with
| (a_tm, ty_sc) -> begin
(

let _79_304 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_79_304) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let _79_313 = (

let _79_307 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_79_307) with
| (return_tm, ty_sc) -> begin
(

let _79_310 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_79_310) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_79_313) with
| (g, return_decl) -> begin
(

let _79_322 = (

let _79_316 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_79_316) with
| (bind_tm, ty_sc) -> begin
(

let _79_319 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_79_319) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_79_322) with
| (g, bind_decl) -> begin
(

let _79_325 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (_79_325) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (_79_327) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _79_331, t, quals, _79_335) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _172_161 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_6 -> (match (_79_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _79_341 -> begin
false
end))))
in (FStar_All.pipe_right _172_161 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(

let _79_345 = (FStar_Syntax_Util.arrow_formals t)
in (match (_79_345) with
| (bs, _79_344) -> begin
(let _172_162 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g lid quals _172_162))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _79_351, _79_353, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _172_165 = (let _172_164 = (let _172_163 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _172_163.FStar_Syntax_Syntax.fv_name)
in _172_164.FStar_Syntax_Syntax.v)
in (extract_typ_abbrev g _172_165 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _79_360, quals) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (

let _79_370 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_79_370) with
| (ml_let, _79_367, _79_369) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _79_373) -> begin
(

let _79_405 = (FStar_List.fold_left2 (fun _79_378 ml_lb _79_388 -> (match (((_79_378), (_79_388))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _79_386; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _79_383; FStar_Syntax_Syntax.lbdef = _79_381}) -> begin
(

let lb_lid = (let _172_170 = (let _172_169 = (FStar_Util.right lbname)
in _172_169.FStar_Syntax_Syntax.fv_name)
in _172_170.FStar_Syntax_Syntax.v)
in (

let _79_402 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_7 -> (match (_79_7) with
| FStar_Syntax_Syntax.Projector (_79_392) -> begin
true
end
| _79_395 -> begin
false
end)))) then begin
(

let mname = (let _172_172 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _172_172 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _172_174 = (FStar_Util.right lbname)
in (let _172_173 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _172_174 mname _172_173 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let _79_398 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), (0)); FStar_Extraction_ML_Syntax.mllb_tysc = _79_398.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _79_398.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _79_398.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _79_398.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _172_177 = (let _172_176 = (let _172_175 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _172_175 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _172_176))
in ((_172_177), (ml_lb)))
end
in (match (_79_402) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_79_405) with
| (g, ml_lbs') -> begin
(

let qual = if (FStar_Util.for_some (fun _79_8 -> (match (_79_8) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _79_409 -> begin
false
end)) quals) then begin
FStar_Extraction_ML_Syntax.Assumed
end else begin
(Prims.fst ml_lbs)
end
in (let _172_181 = (let _172_180 = (let _172_179 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_172_179))
in (_172_180)::(FStar_Extraction_ML_Syntax.MLM_Let (((qual), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_172_181))))
end))
end
| _79_412 -> begin
(let _172_183 = (let _172_182 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _172_182))
in (FStar_All.failwith _172_183))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _79_415, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _172_184 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _172_184 None))
end)
in (let _172_190 = (let _172_189 = (let _172_188 = (let _172_187 = (let _172_186 = (let _172_185 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_172_185))
in {FStar_Syntax_Syntax.lbname = _172_186; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_172_187)::[])
in ((false), (_172_188)))
in ((_172_189), (r), ([]), (quals)))
in FStar_Syntax_Syntax.Sig_let (_172_190)))
in (

let _79_431 = (extract_sig g always_fail)
in (match (_79_431) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _79_9 -> (match (_79_9) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _79_436 -> begin
None
end)))) with
| Some (l) -> begin
(let _172_196 = (let _172_195 = (let _172_192 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_172_192))
in (let _172_194 = (let _172_193 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_172_193)::[])
in (_172_195)::_172_194))
in ((g), (_172_196)))
end
| _79_440 -> begin
(match ((FStar_Util.find_map quals (fun _79_10 -> (match (_79_10) with
| FStar_Syntax_Syntax.Projector (l, _79_444) -> begin
Some (l)
end
| _79_448 -> begin
None
end)))) with
| Some (_79_450) -> begin
((g), ([]))
end
| _79_453 -> begin
((g), (mlm))
end)
end)
end)))
end else begin
((g), ([]))
end
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let _79_463 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_79_463) with
| (ml_main, _79_460, _79_462) -> begin
(let _172_200 = (let _172_199 = (let _172_198 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_172_198))
in (_172_199)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_172_200)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_79_465) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _172_205 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _172_205 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _79_483 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _79_486 = g
in {FStar_Extraction_ML_UEnv.tcenv = _79_486.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _79_486.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _79_486.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _79_490 = (let _172_210 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _172_210))
in (

let _79_494 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_79_494) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end)))
end))))




