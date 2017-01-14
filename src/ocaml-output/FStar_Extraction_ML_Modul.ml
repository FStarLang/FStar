
open Prims

let fail_exp = (fun lid t -> (let _181_16 = (let _181_15 = (let _181_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _181_13 = (let _181_12 = (FStar_Syntax_Syntax.iarg t)
in (let _181_11 = (let _181_10 = (let _181_9 = (let _181_8 = (let _181_7 = (let _181_6 = (let _181_5 = (let _181_4 = (let _181_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _181_3))
in (FStar_Bytes.string_as_unicode_bytes _181_4))
in ((_181_5), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (_181_6))
in FStar_Syntax_Syntax.Tm_constant (_181_7))
in (FStar_Syntax_Syntax.mk _181_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _181_9))
in (_181_10)::[])
in (_181_12)::_181_11))
in ((_181_14), (_181_13))))
in FStar_Syntax_Syntax.Tm_app (_181_15))
in (FStar_Syntax_Syntax.mk _181_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _80_11 -> (match (_80_11) with
| (bv, _80_10) -> begin
(let _181_29 = (let _181_27 = (let _181_26 = (let _181_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_181_25))
in Some (_181_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _181_27))
in (let _181_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_181_29), (_181_28))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def = (let _181_39 = (let _181_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _181_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _181_39 FStar_Syntax_Util.un_uinst))
in (

let def = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_80_19) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| _80_22 -> begin
def
end)
in (

let _80_34 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _80_27) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _80_31 -> begin
(([]), (def))
end)
in (match (_80_34) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___512 -> (match (uu___512) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _80_38 -> begin
false
end)) quals)
in (

let _80_42 = (binders_as_mlty_binders env bs)
in (match (_80_42) with
| (env, ml_bs) -> begin
(

let body = (let _181_41 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _181_41 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let mangled_projector = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___513 -> (match (uu___513) with
| FStar_Syntax_Syntax.Projector (_80_46) -> begin
true
end
| _80_49 -> begin
false
end)))) then begin
(

let mname = (mangle_projector_lid lid)
in Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end else begin
None
end
in (

let td = (((assumed), ((lident_as_mlsymbol lid)), (mangled_projector), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body)))))::[]
in (

let def = (let _181_44 = (let _181_43 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_181_43))
in (_181_44)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___514 -> (match (uu___514) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _80_58 -> begin
false
end)))) then begin
env
end else begin
(FStar_Extraction_ML_UEnv.extend_tydef env fv td)
end
in ((env), (def)))))))
end)))
end))))))


type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}


let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkdata_constructor"))))


type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}


let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkinductive_family"))))


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _181_79 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _181_78 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _181_77 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _181_76 = (let _181_75 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _181_74 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _181_73 = (let _181_72 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _181_72))
in (Prims.strcat _181_74 _181_73))))))
in (FStar_All.pipe_right _181_75 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _181_79 _181_78 _181_77 _181_76))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun uu___516 -> (match (uu___516) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _80_87 = (FStar_Syntax_Subst.open_term bs t)
in (match (_80_87) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun uu___515 -> (match (uu___515) with
| FStar_Syntax_Syntax.Sig_datacon (d, _80_91, t, l', nparams, _80_96, _80_98, _80_100) when (FStar_Ident.lid_equals l l') -> begin
(

let _80_105 = (FStar_Syntax_Util.arrow_formals t)
in (match (_80_105) with
| (bs', body) -> begin
(

let _80_108 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_80_108) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _80_112 _80_116 -> (match (((_80_112), (_80_116))) with
| ((b', _80_111), (b, _80_115)) -> begin
(let _181_88 = (let _181_87 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_181_87)))
in FStar_Syntax_Syntax.NT (_181_88))
end)) bs_params bs)
in (

let t = (let _181_90 = (let _181_89 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _181_89))
in (FStar_All.pipe_right _181_90 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _80_120 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _80_123 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _181_101 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _181_101))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _181_104 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _181_103 = (let _181_102 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_181_102)))
in ((_181_104), (_181_103))))))))
in (

let extract_one_family = (fun env ind -> (

let _80_138 = (binders_as_mlty_binders env ind.iparams)
in (match (_80_138) with
| (env, vars) -> begin
(

let _80_141 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_80_141) with
| (env, ctors) -> begin
(

let _80_145 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_80_145) with
| (indices, _80_144) -> begin
(

let ml_params = (let _181_113 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _80_147 -> (let _181_112 = (let _181_111 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _181_111))
in ((_181_112), ((Prims.parse_int "0")))))))
in (FStar_List.append vars _181_113))
in (

let tbody = (match ((FStar_Util.find_opt (fun uu___517 -> (match (uu___517) with
| FStar_Syntax_Syntax.RecordType (_80_152) -> begin
true
end
| _80_155 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let _80_164 = (FStar_List.hd ctors)
in (match (_80_164) with
| (_80_162, c_ty) -> begin
(

let _80_165 = ()
in (

let fields = (FStar_List.map2 (fun id ty -> (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (((lident_as_mlsymbol lid)), (ty)))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _80_172 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in ((env), (((false), ((lident_as_mlsymbol ind.iname)), (None), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _80_176, t, _80_179, _80_181, _80_183, _80_185, _80_187))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _80_194, r) -> begin
(

let _80_200 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_80_200) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _80_204, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _80_211 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_80_211) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _80_213 -> begin
(failwith "Unexpected signature element")
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _80_217 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _181_122 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" _181_122))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _80_230) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _181_133 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _181_133 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (match ((let _181_136 = (FStar_Syntax_Subst.compress tm)
in _181_136.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _80_246) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let _80_257 = (let _181_137 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _181_137))
in (match (_80_257) with
| (_80_253, tysc, _80_256) -> begin
(let _181_138 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_181_138), (tysc)))
end)))
end
| _80_259 -> begin
(failwith "Not an fv")
end))
in (

let extract_action = (fun g a -> (

let _80_265 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_80_265) with
| (a_tm, ty_sc) -> begin
(

let _80_268 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_80_268) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let _80_277 = (

let _80_271 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_80_271) with
| (return_tm, ty_sc) -> begin
(

let _80_274 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_80_274) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_80_277) with
| (g, return_decl) -> begin
(

let _80_286 = (

let _80_280 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_80_280) with
| (bind_tm, ty_sc) -> begin
(

let _80_283 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_80_283) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_80_286) with
| (g, bind_decl) -> begin
(

let _80_289 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (_80_289) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (_80_291) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _80_295, t, quals, _80_299) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
if (let _181_144 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___518 -> (match (uu___518) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _80_305 -> begin
false
end))))
in (FStar_All.pipe_right _181_144 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(

let _80_309 = (FStar_Syntax_Util.arrow_formals t)
in (match (_80_309) with
| (bs, _80_308) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (let _181_145 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals _181_145)))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _80_316, _80_318, quals, _80_321) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(let _181_146 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g _181_146 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _80_327, quals, attrs) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (

let _80_338 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_80_338) with
| (ml_let, _80_335, _80_337) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _80_341, bindings), _80_345) -> begin
(

let _80_377 = (FStar_List.fold_left2 (fun _80_350 ml_lb _80_360 -> (match (((_80_350), (_80_360))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _80_358; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _80_355; FStar_Syntax_Syntax.lbdef = _80_353}) -> begin
(

let lb_lid = (let _181_151 = (let _181_150 = (FStar_Util.right lbname)
in _181_150.FStar_Syntax_Syntax.fv_name)
in _181_151.FStar_Syntax_Syntax.v)
in (

let _80_374 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___519 -> (match (uu___519) with
| FStar_Syntax_Syntax.Projector (_80_364) -> begin
true
end
| _80_367 -> begin
false
end)))) then begin
(

let mname = (FStar_All.pipe_right (mangle_projector_lid lb_lid) FStar_Extraction_ML_Syntax.mlpath_of_lident)
in (

let env = (let _181_154 = (FStar_Util.right lbname)
in (let _181_153 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _181_154 mname _181_153 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let _80_370 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _80_370.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_370.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _80_370.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _80_370.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _181_157 = (let _181_156 = (let _181_155 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _181_155 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _181_156))
in ((_181_157), (ml_lb)))
end
in (match (_80_374) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_80_377) with
| (g, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun uu___520 -> (match (uu___520) with
| FStar_Syntax_Syntax.Assumption -> begin
Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| _80_383 -> begin
None
end)) quals)
in (

let flags' = (FStar_List.choose (fun uu___521 -> (match (uu___521) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, _80_394)); FStar_Syntax_Syntax.tk = _80_391; FStar_Syntax_Syntax.pos = _80_389; FStar_Syntax_Syntax.vars = _80_387} -> begin
Some (FStar_Extraction_ML_Syntax.Attribute ((FStar_Util.string_of_unicode data)))
end
| _80_400 -> begin
(

let _80_401 = (FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message")
in None)
end)) attrs)
in (let _181_162 = (let _181_161 = (let _181_160 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_181_160))
in (_181_161)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_181_162)))))
end))
end
| _80_405 -> begin
(let _181_164 = (let _181_163 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _181_163))
in (failwith _181_164))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _80_408, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _181_165 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _181_165 None))
end)
in (let _181_171 = (let _181_170 = (let _181_169 = (let _181_168 = (let _181_167 = (let _181_166 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_181_166))
in {FStar_Syntax_Syntax.lbname = _181_167; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_181_168)::[])
in ((false), (_181_169)))
in ((_181_170), (r), ([]), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_181_171)))
in (

let _80_424 = (extract_sig g always_fail)
in (match (_80_424) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun uu___522 -> (match (uu___522) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _80_429 -> begin
None
end)))) with
| Some (l) -> begin
(let _181_177 = (let _181_176 = (let _181_173 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_181_173))
in (let _181_175 = (let _181_174 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_181_174)::[])
in (_181_176)::_181_175))
in ((g), (_181_177)))
end
| _80_433 -> begin
(match ((FStar_Util.find_map quals (fun uu___523 -> (match (uu___523) with
| FStar_Syntax_Syntax.Projector (l, _80_437) -> begin
Some (l)
end
| _80_441 -> begin
None
end)))) with
| Some (_80_443) -> begin
((g), ([]))
end
| _80_446 -> begin
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

let _80_456 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_80_456) with
| (ml_main, _80_453, _80_455) -> begin
(let _181_181 = (let _181_180 = (let _181_179 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_181_179))
in (_181_180)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_181_181)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_80_458) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _181_186 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _181_186 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _80_476 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _80_479 = g
in {FStar_Extraction_ML_UEnv.tcenv = _80_479.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _80_479.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _80_479.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in (

let _80_484 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_80_484) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str <> "Prims") && (not (m.FStar_Syntax_Syntax.is_interface))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let _80_486 = (let _181_191 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" _181_191))
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end else begin
((g), ([]))
end)
end))))))




