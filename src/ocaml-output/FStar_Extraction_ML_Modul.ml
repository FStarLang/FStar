
open Prims

let fail_exp = (fun lid t -> (let _175_16 = (let _175_15 = (let _175_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _175_13 = (let _175_12 = (FStar_Syntax_Syntax.iarg t)
in (let _175_11 = (let _175_10 = (let _175_9 = (let _175_8 = (let _175_7 = (let _175_6 = (let _175_5 = (let _175_4 = (let _175_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _175_3))
in (FStar_Bytes.string_as_unicode_bytes _175_4))
in ((_175_5), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (_175_6))
in FStar_Syntax_Syntax.Tm_constant (_175_7))
in (FStar_Syntax_Syntax.mk _175_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _175_9))
in (_175_10)::[])
in (_175_12)::_175_11))
in ((_175_14), (_175_13))))
in FStar_Syntax_Syntax.Tm_app (_175_15))
in (FStar_Syntax_Syntax.mk _175_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _80_23 -> (match (_80_23) with
| (bv, _80_22) -> begin
(let _175_29 = (let _175_27 = (let _175_26 = (let _175_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_175_25))
in Some (_175_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _175_27))
in (let _175_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_175_29), (_175_28))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def = (let _175_39 = (let _175_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _175_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _175_39 FStar_Syntax_Util.un_uinst))
in (

let def = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_80_31) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| _80_34 -> begin
def
end)
in (

let _80_46 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _80_39) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _80_43 -> begin
(([]), (def))
end)
in (match (_80_46) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun _80_1 -> (match (_80_1) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _80_50 -> begin
false
end)) quals)
in (

let _80_54 = (binders_as_mlty_binders env bs)
in (match (_80_54) with
| (env, ml_bs) -> begin
(

let body = (let _175_41 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _175_41 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let mangled_projector = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_2 -> (match (_80_2) with
| FStar_Syntax_Syntax.Projector (_80_58) -> begin
true
end
| _80_61 -> begin
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

let def = (let _175_44 = (let _175_43 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_175_43))
in (_175_44)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_3 -> (match (_80_3) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _80_70 -> begin
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


let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))


type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}


let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _175_79 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _175_78 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _175_77 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _175_76 = (let _175_75 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _175_74 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _175_73 = (let _175_72 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _175_72))
in (Prims.strcat _175_74 _175_73))))))
in (FStar_All.pipe_right _175_75 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _175_79 _175_78 _175_77 _175_76))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _80_5 -> (match (_80_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _80_99 = (FStar_Syntax_Subst.open_term bs t)
in (match (_80_99) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _80_4 -> (match (_80_4) with
| FStar_Syntax_Syntax.Sig_datacon (d, _80_103, t, l', nparams, _80_108, _80_110, _80_112) when (FStar_Ident.lid_equals l l') -> begin
(

let _80_117 = (FStar_Syntax_Util.arrow_formals t)
in (match (_80_117) with
| (bs', body) -> begin
(

let _80_120 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_80_120) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _80_124 _80_128 -> (match (((_80_124), (_80_128))) with
| ((b', _80_123), (b, _80_127)) -> begin
(let _175_88 = (let _175_87 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_175_87)))
in FStar_Syntax_Syntax.NT (_175_88))
end)) bs_params bs)
in (

let t = (let _175_90 = (let _175_89 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _175_89))
in (FStar_All.pipe_right _175_90 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _80_132 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _80_135 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _175_101 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _175_101))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _175_104 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _175_103 = (let _175_102 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_175_102)))
in ((_175_104), (_175_103))))))))
in (

let extract_one_family = (fun env ind -> (

let _80_150 = (binders_as_mlty_binders env ind.iparams)
in (match (_80_150) with
| (env, vars) -> begin
(

let _80_153 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_80_153) with
| (env, ctors) -> begin
(

let _80_157 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_80_157) with
| (indices, _80_156) -> begin
(

let ml_params = (let _175_113 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _80_159 -> (let _175_112 = (let _175_111 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _175_111))
in ((_175_112), ((Prims.parse_int "0")))))))
in (FStar_List.append vars _175_113))
in (

let tbody = (match ((FStar_Util.find_opt (fun _80_6 -> (match (_80_6) with
| FStar_Syntax_Syntax.RecordType (_80_164) -> begin
true
end
| _80_167 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let _80_176 = (FStar_List.hd ctors)
in (match (_80_176) with
| (_80_174, c_ty) -> begin
(

let _80_177 = ()
in (

let fields = (FStar_List.map2 (fun id ty -> (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (((lident_as_mlsymbol lid)), (ty)))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _80_184 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in ((env), (((false), ((lident_as_mlsymbol ind.iname)), (None), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _80_188, t, _80_191, _80_193, _80_195, _80_197, _80_199))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _80_206, r) -> begin
(

let _80_212 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_80_212) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _80_216, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _80_223 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_80_223) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _80_225 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))


let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (

let l = (fun _80_7 -> (match (_80_7) with
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
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _80_244, t, quals, _80_248) -> begin
(let _175_126 = (FStar_Syntax_Print.lid_to_string lid)
in (let _175_125 = (let _175_124 = (let _175_123 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _175_123))
in (l _175_124))
in (FStar_Util.print2 "\t\t%s @ %s\n" _175_126 _175_125)))
end
| FStar_Syntax_Syntax.Sig_let ((_80_252, (lb)::_80_254), _80_259, _80_261, _80_263) -> begin
(let _175_134 = (let _175_129 = (let _175_128 = (let _175_127 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _175_127.FStar_Syntax_Syntax.fv_name)
in _175_128.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _175_129 FStar_Syntax_Print.lid_to_string))
in (let _175_133 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _175_132 = (let _175_131 = (let _175_130 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _175_130))
in (l _175_131))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _175_134 _175_133 _175_132))))
end
| _80_267 -> begin
(FStar_Util.print_string "other\n")
end)))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _80_273 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (

let _80_271 = (let _175_141 = (let _175_140 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _175_140))
in (FStar_Util.print_string _175_141))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _80_286) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _175_152 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _175_152 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (match ((let _175_155 = (FStar_Syntax_Subst.compress tm)
in _175_155.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _80_302) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let _80_313 = (let _175_156 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _175_156))
in (match (_80_313) with
| (_80_309, tysc, _80_312) -> begin
(let _175_157 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_175_157), (tysc)))
end)))
end
| _80_315 -> begin
(FStar_All.failwith "Not an fv")
end))
in (

let extract_action = (fun g a -> (

let _80_321 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_80_321) with
| (a_tm, ty_sc) -> begin
(

let _80_324 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_80_324) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let _80_333 = (

let _80_327 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_80_327) with
| (return_tm, ty_sc) -> begin
(

let _80_330 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_80_330) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_80_333) with
| (g, return_decl) -> begin
(

let _80_342 = (

let _80_336 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_80_336) with
| (bind_tm, ty_sc) -> begin
(

let _80_339 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_80_339) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_80_342) with
| (g, bind_decl) -> begin
(

let _80_345 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (_80_345) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (_80_347) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _80_351, t, quals, _80_355) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _175_163 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_8 -> (match (_80_8) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _80_361 -> begin
false
end))))
in (FStar_All.pipe_right _175_163 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(

let _80_365 = (FStar_Syntax_Util.arrow_formals t)
in (match (_80_365) with
| (bs, _80_364) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (let _175_164 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals _175_164)))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _80_372, _80_374, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _175_165 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g _175_165 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _80_381, quals) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (

let _80_391 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_80_391) with
| (ml_let, _80_388, _80_390) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _80_394, bindings), _80_398) -> begin
(

let _80_430 = (FStar_List.fold_left2 (fun _80_403 ml_lb _80_413 -> (match (((_80_403), (_80_413))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _80_411; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _80_408; FStar_Syntax_Syntax.lbdef = _80_406}) -> begin
(

let lb_lid = (let _175_170 = (let _175_169 = (FStar_Util.right lbname)
in _175_169.FStar_Syntax_Syntax.fv_name)
in _175_170.FStar_Syntax_Syntax.v)
in (

let _80_427 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_9 -> (match (_80_9) with
| FStar_Syntax_Syntax.Projector (_80_417) -> begin
true
end
| _80_420 -> begin
false
end)))) then begin
(

let mname = (FStar_All.pipe_right (mangle_projector_lid lb_lid) FStar_Extraction_ML_Syntax.mlpath_of_lident)
in (

let env = (let _175_173 = (FStar_Util.right lbname)
in (let _175_172 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _175_173 mname _175_172 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let _80_423 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _80_423.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_423.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _80_423.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _80_423.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _175_176 = (let _175_175 = (let _175_174 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _175_174 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _175_175))
in ((_175_176), (ml_lb)))
end
in (match (_80_427) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_80_430) with
| (g, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun _80_10 -> (match (_80_10) with
| FStar_Syntax_Syntax.Assumption -> begin
Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| _80_436 -> begin
None
end)) quals)
in (let _175_180 = (let _175_179 = (let _175_178 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_175_178))
in (_175_179)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), (flags), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_175_180))))
end))
end
| _80_439 -> begin
(let _175_182 = (let _175_181 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _175_181))
in (FStar_All.failwith _175_182))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _80_442, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _175_183 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _175_183 None))
end)
in (let _175_189 = (let _175_188 = (let _175_187 = (let _175_186 = (let _175_185 = (let _175_184 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_175_184))
in {FStar_Syntax_Syntax.lbname = _175_185; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_175_186)::[])
in ((false), (_175_187)))
in ((_175_188), (r), ([]), (quals)))
in FStar_Syntax_Syntax.Sig_let (_175_189)))
in (

let _80_458 = (extract_sig g always_fail)
in (match (_80_458) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _80_11 -> (match (_80_11) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _80_463 -> begin
None
end)))) with
| Some (l) -> begin
(let _175_195 = (let _175_194 = (let _175_191 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_175_191))
in (let _175_193 = (let _175_192 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_175_192)::[])
in (_175_194)::_175_193))
in ((g), (_175_195)))
end
| _80_467 -> begin
(match ((FStar_Util.find_map quals (fun _80_12 -> (match (_80_12) with
| FStar_Syntax_Syntax.Projector (l, _80_471) -> begin
Some (l)
end
| _80_475 -> begin
None
end)))) with
| Some (_80_477) -> begin
((g), ([]))
end
| _80_480 -> begin
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

let _80_490 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_80_490) with
| (ml_main, _80_487, _80_489) -> begin
(let _175_199 = (let _175_198 = (let _175_197 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_175_197))
in (_175_198)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_175_199)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_80_492) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _175_204 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _175_204 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _80_510 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _80_513 = g
in {FStar_Extraction_ML_UEnv.tcenv = _80_513.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _80_513.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _80_513.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _80_517 = (let _175_209 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _175_209))
in (

let _80_521 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_80_521) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end)))
end))))




