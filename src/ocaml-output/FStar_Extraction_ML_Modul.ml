
open Prims

let fail_exp = (fun lid t -> (let _177_16 = (let _177_15 = (let _177_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _177_13 = (let _177_12 = (FStar_Syntax_Syntax.iarg t)
in (let _177_11 = (let _177_10 = (let _177_9 = (let _177_8 = (let _177_7 = (let _177_6 = (let _177_5 = (let _177_4 = (let _177_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _177_3))
in (FStar_Bytes.string_as_unicode_bytes _177_4))
in ((_177_5), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (_177_6))
in FStar_Syntax_Syntax.Tm_constant (_177_7))
in (FStar_Syntax_Syntax.mk _177_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _177_9))
in (_177_10)::[])
in (_177_12)::_177_11))
in ((_177_14), (_177_13))))
in FStar_Syntax_Syntax.Tm_app (_177_15))
in (FStar_Syntax_Syntax.mk _177_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _80_18 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_80_18) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Ident.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _80_27 -> (match (_80_27) with
| (bv, _80_26) -> begin
(let _177_29 = (let _177_27 = (let _177_26 = (let _177_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_177_25))
in Some (_177_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _177_27))
in (let _177_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_177_29), (_177_28))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env lid quals def -> (

let def = (let _177_39 = (let _177_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _177_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _177_39 FStar_Syntax_Util.un_uinst))
in (

let def = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_80_34) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| _80_37 -> begin
def
end)
in (

let _80_49 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _80_42) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _80_46 -> begin
(([]), (def))
end)
in (match (_80_49) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun _80_1 -> (match (_80_1) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _80_53 -> begin
false
end)) quals)
in (

let _80_57 = (binders_as_mlty_binders env bs)
in (match (_80_57) with
| (env, ml_bs) -> begin
(

let body = (let _177_41 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _177_41 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let td = (((assumed), ((lident_as_mlsymbol lid)), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body)))))::[]
in (

let def = (let _177_43 = (let _177_42 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_177_42))
in (_177_43)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_2 -> (match (_80_2) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _80_65 -> begin
false
end)))) then begin
env
end else begin
(FStar_Extraction_ML_UEnv.extend_tydef env td)
end
in ((env), (def))))))
end)))
end)))))


type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}


let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))


type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}


let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _177_78 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _177_77 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _177_76 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _177_75 = (let _177_74 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _177_73 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _177_72 = (let _177_71 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _177_71))
in (Prims.strcat _177_73 _177_72))))))
in (FStar_All.pipe_right _177_74 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _177_78 _177_77 _177_76 _177_75))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _80_4 -> (match (_80_4) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _80_94 = (FStar_Syntax_Subst.open_term bs t)
in (match (_80_94) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _80_3 -> (match (_80_3) with
| FStar_Syntax_Syntax.Sig_datacon (d, _80_98, t, l', nparams, _80_103, _80_105, _80_107) when (FStar_Ident.lid_equals l l') -> begin
(

let _80_112 = (FStar_Syntax_Util.arrow_formals t)
in (match (_80_112) with
| (bs', body) -> begin
(

let _80_115 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_80_115) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _80_119 _80_123 -> (match (((_80_119), (_80_123))) with
| ((b', _80_118), (b, _80_122)) -> begin
(let _177_87 = (let _177_86 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_177_86)))
in FStar_Syntax_Syntax.NT (_177_87))
end)) bs_params bs)
in (

let t = (let _177_89 = (let _177_88 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _177_88))
in (FStar_All.pipe_right _177_89 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _80_127 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _80_130 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _177_100 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _177_100))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _177_103 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _177_102 = (let _177_101 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_177_101)))
in ((_177_103), (_177_102))))))))
in (

let extract_one_family = (fun env ind -> (

let _80_145 = (binders_as_mlty_binders env ind.iparams)
in (match (_80_145) with
| (env, vars) -> begin
(

let _80_148 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_80_148) with
| (env, ctors) -> begin
(

let _80_152 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_80_152) with
| (indices, _80_151) -> begin
(

let ml_params = (let _177_112 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _80_154 -> (let _177_111 = (let _177_110 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _177_110))
in ((_177_111), ((Prims.parse_int "0")))))))
in (FStar_List.append vars _177_112))
in (

let tbody = (match ((FStar_Util.find_opt (fun _80_5 -> (match (_80_5) with
| FStar_Syntax_Syntax.RecordType (_80_159) -> begin
true
end
| _80_162 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(

let _80_169 = (FStar_List.hd ctors)
in (match (_80_169) with
| (_80_167, c_ty) -> begin
(

let _80_170 = ()
in (

let fields = (FStar_List.map2 (fun lid ty -> (((lident_as_mlsymbol lid)), (ty))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _80_176 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in ((env), (((false), ((lident_as_mlsymbol ind.iname)), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _80_180, t, _80_183, _80_185, _80_187, _80_189, _80_191))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _80_198, r) -> begin
(

let _80_204 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_80_204) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _80_208, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _80_215 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_80_215) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _80_217 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))


let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (

let l = (fun _80_6 -> (match (_80_6) with
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
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _80_236, t, quals, _80_240) -> begin
(let _177_125 = (FStar_Syntax_Print.lid_to_string lid)
in (let _177_124 = (let _177_123 = (let _177_122 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _177_122))
in (l _177_123))
in (FStar_Util.print2 "\t\t%s @ %s\n" _177_125 _177_124)))
end
| FStar_Syntax_Syntax.Sig_let ((_80_244, (lb)::_80_246), _80_251, _80_253, _80_255) -> begin
(let _177_133 = (let _177_128 = (let _177_127 = (let _177_126 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _177_126.FStar_Syntax_Syntax.fv_name)
in _177_127.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_128 FStar_Syntax_Print.lid_to_string))
in (let _177_132 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _177_131 = (let _177_130 = (let _177_129 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _177_129))
in (l _177_130))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _177_133 _177_132 _177_131))))
end
| _80_259 -> begin
(FStar_Util.print_string "other\n")
end)))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _80_265 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (

let _80_263 = (let _177_140 = (let _177_139 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _177_139))
in (FStar_Util.print_string _177_140))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _80_278) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _177_151 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _177_151 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NoLetQualifier), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (match ((let _177_154 = (FStar_Syntax_Subst.compress tm)
in _177_154.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _80_294) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let _80_305 = (let _177_155 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _177_155))
in (match (_80_305) with
| (_80_301, tysc, _80_304) -> begin
(let _177_156 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_177_156), (tysc)))
end)))
end
| _80_307 -> begin
(FStar_All.failwith "Not an fv")
end))
in (

let extract_action = (fun g a -> (

let _80_313 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_80_313) with
| (a_tm, ty_sc) -> begin
(

let _80_316 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_80_316) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let _80_325 = (

let _80_319 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_80_319) with
| (return_tm, ty_sc) -> begin
(

let _80_322 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_80_322) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_80_325) with
| (g, return_decl) -> begin
(

let _80_334 = (

let _80_328 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_80_328) with
| (bind_tm, ty_sc) -> begin
(

let _80_331 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_80_331) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_80_334) with
| (g, bind_decl) -> begin
(

let _80_337 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (_80_337) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (_80_339) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _80_343, t, quals, _80_347) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _177_162 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_7 -> (match (_80_7) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _80_353 -> begin
false
end))))
in (FStar_All.pipe_right _177_162 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(

let _80_357 = (FStar_Syntax_Util.arrow_formals t)
in (match (_80_357) with
| (bs, _80_356) -> begin
(let _177_163 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g lid quals _177_163))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _80_363, _80_365, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _177_166 = (let _177_165 = (let _177_164 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _177_164.FStar_Syntax_Syntax.fv_name)
in _177_165.FStar_Syntax_Syntax.v)
in (extract_typ_abbrev g _177_166 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _80_372, quals) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (

let _80_382 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_80_382) with
| (ml_let, _80_379, _80_381) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _80_385) -> begin
(

let _80_417 = (FStar_List.fold_left2 (fun _80_390 ml_lb _80_400 -> (match (((_80_390), (_80_400))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _80_398; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _80_395; FStar_Syntax_Syntax.lbdef = _80_393}) -> begin
(

let lb_lid = (let _177_171 = (let _177_170 = (FStar_Util.right lbname)
in _177_170.FStar_Syntax_Syntax.fv_name)
in _177_171.FStar_Syntax_Syntax.v)
in (

let _80_414 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_8 -> (match (_80_8) with
| FStar_Syntax_Syntax.Projector (_80_404) -> begin
true
end
| _80_407 -> begin
false
end)))) then begin
(

let mname = (let _177_173 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _177_173 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _177_175 = (FStar_Util.right lbname)
in (let _177_174 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _177_175 mname _177_174 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let _80_410 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _80_410.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_410.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _80_410.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _80_410.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _177_178 = (let _177_177 = (let _177_176 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _177_176 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _177_177))
in ((_177_178), (ml_lb)))
end
in (match (_80_414) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_80_417) with
| (g, ml_lbs') -> begin
(

let qual = if (FStar_Util.for_some (fun _80_9 -> (match (_80_9) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _80_421 -> begin
false
end)) quals) then begin
FStar_Extraction_ML_Syntax.Assumed
end else begin
(Prims.fst ml_lbs)
end
in (let _177_182 = (let _177_181 = (let _177_180 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_177_180))
in (_177_181)::(FStar_Extraction_ML_Syntax.MLM_Let (((qual), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_177_182))))
end))
end
| _80_424 -> begin
(let _177_184 = (let _177_183 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _177_183))
in (FStar_All.failwith _177_184))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _80_427, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _177_185 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _177_185 None))
end)
in (let _177_191 = (let _177_190 = (let _177_189 = (let _177_188 = (let _177_187 = (let _177_186 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_177_186))
in {FStar_Syntax_Syntax.lbname = _177_187; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_177_188)::[])
in ((false), (_177_189)))
in ((_177_190), (r), ([]), (quals)))
in FStar_Syntax_Syntax.Sig_let (_177_191)))
in (

let _80_443 = (extract_sig g always_fail)
in (match (_80_443) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _80_10 -> (match (_80_10) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _80_448 -> begin
None
end)))) with
| Some (l) -> begin
(let _177_197 = (let _177_196 = (let _177_193 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_177_193))
in (let _177_195 = (let _177_194 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_177_194)::[])
in (_177_196)::_177_195))
in ((g), (_177_197)))
end
| _80_452 -> begin
(match ((FStar_Util.find_map quals (fun _80_11 -> (match (_80_11) with
| FStar_Syntax_Syntax.Projector (l, _80_456) -> begin
Some (l)
end
| _80_460 -> begin
None
end)))) with
| Some (_80_462) -> begin
((g), ([]))
end
| _80_465 -> begin
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

let _80_475 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_80_475) with
| (ml_main, _80_472, _80_474) -> begin
(let _177_201 = (let _177_200 = (let _177_199 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_177_199))
in (_177_200)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_177_201)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_80_477) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _177_206 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _177_206 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _80_495 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _80_498 = g
in {FStar_Extraction_ML_UEnv.tcenv = _80_498.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _80_498.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _80_498.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _80_502 = (let _177_211 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _177_211))
in (

let _80_506 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_80_506) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end)))
end))))




