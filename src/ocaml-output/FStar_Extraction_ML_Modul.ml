
open Prims

let fail_exp = (fun lid t -> (let _180_16 = (let _180_15 = (let _180_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _180_13 = (let _180_12 = (FStar_Syntax_Syntax.iarg t)
in (let _180_11 = (let _180_10 = (let _180_9 = (let _180_8 = (let _180_7 = (let _180_6 = (let _180_5 = (let _180_4 = (let _180_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _180_3))
in (FStar_Bytes.string_as_unicode_bytes _180_4))
in ((_180_5), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (_180_6))
in FStar_Syntax_Syntax.Tm_constant (_180_7))
in (FStar_Syntax_Syntax.mk _180_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _180_9))
in (_180_10)::[])
in (_180_12)::_180_11))
in ((_180_14), (_180_13))))
in FStar_Syntax_Syntax.Tm_app (_180_15))
in (FStar_Syntax_Syntax.mk _180_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _82_23 -> (match (_82_23) with
| (bv, _82_22) -> begin
(let _180_29 = (let _180_27 = (let _180_26 = (let _180_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_180_25))
in Some (_180_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _180_27))
in (let _180_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_180_29), (_180_28))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def = (let _180_39 = (let _180_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _180_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _180_39 FStar_Syntax_Util.un_uinst))
in (

let def = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_82_31) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| _82_34 -> begin
def
end)
in (

let _82_46 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _82_39) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _82_43 -> begin
(([]), (def))
end)
in (match (_82_46) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun _82_1 -> (match (_82_1) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _82_50 -> begin
false
end)) quals)
in (

let _82_54 = (binders_as_mlty_binders env bs)
in (match (_82_54) with
| (env, ml_bs) -> begin
(

let body = (let _180_41 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _180_41 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let mangled_projector = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _82_2 -> (match (_82_2) with
| FStar_Syntax_Syntax.Projector (_82_58) -> begin
true
end
| _82_61 -> begin
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

let def = (let _180_44 = (let _180_43 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_180_43))
in (_180_44)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _82_3 -> (match (_82_3) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _82_70 -> begin
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


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _180_79 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _180_78 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _180_77 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _180_76 = (let _180_75 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _180_74 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _180_73 = (let _180_72 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _180_72))
in (Prims.strcat _180_74 _180_73))))))
in (FStar_All.pipe_right _180_75 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _180_79 _180_78 _180_77 _180_76))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _82_5 -> (match (_82_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _82_99 = (FStar_Syntax_Subst.open_term bs t)
in (match (_82_99) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _82_4 -> (match (_82_4) with
| FStar_Syntax_Syntax.Sig_datacon (d, _82_103, t, l', nparams, _82_108, _82_110, _82_112) when (FStar_Ident.lid_equals l l') -> begin
(

let _82_117 = (FStar_Syntax_Util.arrow_formals t)
in (match (_82_117) with
| (bs', body) -> begin
(

let _82_120 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_82_120) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _82_124 _82_128 -> (match (((_82_124), (_82_128))) with
| ((b', _82_123), (b, _82_127)) -> begin
(let _180_88 = (let _180_87 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_180_87)))
in FStar_Syntax_Syntax.NT (_180_88))
end)) bs_params bs)
in (

let t = (let _180_90 = (let _180_89 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _180_89))
in (FStar_All.pipe_right _180_90 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _82_132 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _82_135 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _180_101 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _180_101))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _180_104 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _180_103 = (let _180_102 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_180_102)))
in ((_180_104), (_180_103))))))))
in (

let extract_one_family = (fun env ind -> (

let _82_150 = (binders_as_mlty_binders env ind.iparams)
in (match (_82_150) with
| (env, vars) -> begin
(

let _82_153 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_82_153) with
| (env, ctors) -> begin
(

let _82_157 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_82_157) with
| (indices, _82_156) -> begin
(

let ml_params = (let _180_113 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _82_159 -> (let _180_112 = (let _180_111 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _180_111))
in ((_180_112), ((Prims.parse_int "0")))))))
in (FStar_List.append vars _180_113))
in (

let tbody = (match ((FStar_Util.find_opt (fun _82_6 -> (match (_82_6) with
| FStar_Syntax_Syntax.RecordType (_82_164) -> begin
true
end
| _82_167 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let _82_176 = (FStar_List.hd ctors)
in (match (_82_176) with
| (_82_174, c_ty) -> begin
(

let _82_177 = ()
in (

let fields = (FStar_List.map2 (fun id ty -> (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (((lident_as_mlsymbol lid)), (ty)))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _82_184 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in ((env), (((false), ((lident_as_mlsymbol ind.iname)), (None), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _82_188, t, _82_191, _82_193, _82_195, _82_197, _82_199))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _82_206, r) -> begin
(

let _82_212 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_82_212) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _82_216, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _82_223 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_82_223) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _82_225 -> begin
(failwith "Unexpected signature element")
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _82_229 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _180_122 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" _180_122))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _82_242) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _180_133 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _180_133 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (match ((let _180_136 = (FStar_Syntax_Subst.compress tm)
in _180_136.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _82_258) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let _82_269 = (let _180_137 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _180_137))
in (match (_82_269) with
| (_82_265, tysc, _82_268) -> begin
(let _180_138 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_180_138), (tysc)))
end)))
end
| _82_271 -> begin
(failwith "Not an fv")
end))
in (

let extract_action = (fun g a -> (

let _82_277 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_82_277) with
| (a_tm, ty_sc) -> begin
(

let _82_280 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_82_280) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let _82_289 = (

let _82_283 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_82_283) with
| (return_tm, ty_sc) -> begin
(

let _82_286 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_82_286) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_82_289) with
| (g, return_decl) -> begin
(

let _82_298 = (

let _82_292 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_82_292) with
| (bind_tm, ty_sc) -> begin
(

let _82_295 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_82_295) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_82_298) with
| (g, bind_decl) -> begin
(

let _82_301 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (_82_301) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (_82_303) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _82_307, t, quals, _82_311) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
if (let _180_144 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _82_7 -> (match (_82_7) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _82_317 -> begin
false
end))))
in (FStar_All.pipe_right _180_144 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(

let _82_321 = (FStar_Syntax_Util.arrow_formals t)
in (match (_82_321) with
| (bs, _82_320) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (let _180_145 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals _180_145)))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _82_328, _82_330, quals, _82_333) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(let _180_146 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g _180_146 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _82_339, quals, attrs) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (

let _82_350 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_82_350) with
| (ml_let, _82_347, _82_349) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _82_353, bindings), _82_357) -> begin
(

let _82_389 = (FStar_List.fold_left2 (fun _82_362 ml_lb _82_372 -> (match (((_82_362), (_82_372))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _82_370; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _82_367; FStar_Syntax_Syntax.lbdef = _82_365}) -> begin
(

let lb_lid = (let _180_151 = (let _180_150 = (FStar_Util.right lbname)
in _180_150.FStar_Syntax_Syntax.fv_name)
in _180_151.FStar_Syntax_Syntax.v)
in (

let _82_386 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _82_8 -> (match (_82_8) with
| FStar_Syntax_Syntax.Projector (_82_376) -> begin
true
end
| _82_379 -> begin
false
end)))) then begin
(

let mname = (FStar_All.pipe_right (mangle_projector_lid lb_lid) FStar_Extraction_ML_Syntax.mlpath_of_lident)
in (

let env = (let _180_154 = (FStar_Util.right lbname)
in (let _180_153 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _180_154 mname _180_153 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let _82_382 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _82_382.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _82_382.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _82_382.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _82_382.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _180_157 = (let _180_156 = (let _180_155 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _180_155 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _180_156))
in ((_180_157), (ml_lb)))
end
in (match (_82_386) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_82_389) with
| (g, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun _82_9 -> (match (_82_9) with
| FStar_Syntax_Syntax.Assumption -> begin
Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| _82_395 -> begin
None
end)) quals)
in (

let flags' = (FStar_List.choose (fun _82_10 -> (match (_82_10) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, _82_406)); FStar_Syntax_Syntax.tk = _82_403; FStar_Syntax_Syntax.pos = _82_401; FStar_Syntax_Syntax.vars = _82_399} -> begin
Some (FStar_Extraction_ML_Syntax.Attribute ((FStar_Util.string_of_unicode data)))
end
| _82_412 -> begin
(

let _82_413 = (FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message")
in None)
end)) attrs)
in (let _180_162 = (let _180_161 = (let _180_160 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_180_160))
in (_180_161)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_180_162)))))
end))
end
| _82_417 -> begin
(let _180_164 = (let _180_163 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _180_163))
in (failwith _180_164))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _82_420, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _180_165 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _180_165 None))
end)
in (let _180_171 = (let _180_170 = (let _180_169 = (let _180_168 = (let _180_167 = (let _180_166 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_180_166))
in {FStar_Syntax_Syntax.lbname = _180_167; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_180_168)::[])
in ((false), (_180_169)))
in ((_180_170), (r), ([]), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_180_171)))
in (

let _82_436 = (extract_sig g always_fail)
in (match (_82_436) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _82_11 -> (match (_82_11) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _82_441 -> begin
None
end)))) with
| Some (l) -> begin
(let _180_177 = (let _180_176 = (let _180_173 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_180_173))
in (let _180_175 = (let _180_174 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_180_174)::[])
in (_180_176)::_180_175))
in ((g), (_180_177)))
end
| _82_445 -> begin
(match ((FStar_Util.find_map quals (fun _82_12 -> (match (_82_12) with
| FStar_Syntax_Syntax.Projector (l, _82_449) -> begin
Some (l)
end
| _82_453 -> begin
None
end)))) with
| Some (_82_455) -> begin
((g), ([]))
end
| _82_458 -> begin
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

let _82_468 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_82_468) with
| (ml_main, _82_465, _82_467) -> begin
(let _180_181 = (let _180_180 = (let _180_179 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_180_179))
in (_180_180)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_180_181)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_82_470) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _180_186 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _180_186 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _82_488 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _82_491 = g
in {FStar_Extraction_ML_UEnv.tcenv = _82_491.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _82_491.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _82_491.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in (

let _82_496 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_82_496) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str <> "Prims") && (not (m.FStar_Syntax_Syntax.is_interface))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let _82_498 = (let _180_191 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" _180_191))
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end else begin
((g), ([]))
end)
end))))))




