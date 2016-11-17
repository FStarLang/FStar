
open Prims

let fail_exp = (fun lid t -> (let _179_16 = (let _179_15 = (let _179_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _179_13 = (let _179_12 = (FStar_Syntax_Syntax.iarg t)
in (let _179_11 = (let _179_10 = (let _179_9 = (let _179_8 = (let _179_7 = (let _179_6 = (let _179_5 = (let _179_4 = (let _179_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _179_3))
in (FStar_Bytes.string_as_unicode_bytes _179_4))
in ((_179_5), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (_179_6))
in FStar_Syntax_Syntax.Tm_constant (_179_7))
in (FStar_Syntax_Syntax.mk _179_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _179_9))
in (_179_10)::[])
in (_179_12)::_179_11))
in ((_179_14), (_179_13))))
in FStar_Syntax_Syntax.Tm_app (_179_15))
in (FStar_Syntax_Syntax.mk _179_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _82_20 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_82_20) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Ident.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _82_29 -> (match (_82_29) with
| (bv, _82_28) -> begin
(let _179_29 = (let _179_27 = (let _179_26 = (let _179_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_179_25))
in Some (_179_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _179_27))
in (let _179_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_179_29), (_179_28))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def = (let _179_39 = (let _179_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _179_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _179_39 FStar_Syntax_Util.un_uinst))
in (

let def = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_82_37) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| _82_40 -> begin
def
end)
in (

let _82_52 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _82_45) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _82_49 -> begin
(([]), (def))
end)
in (match (_82_52) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun _82_1 -> (match (_82_1) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _82_56 -> begin
false
end)) quals)
in (

let _82_60 = (binders_as_mlty_binders env bs)
in (match (_82_60) with
| (env, ml_bs) -> begin
(

let body = (let _179_41 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _179_41 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let mangled_projector = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _82_2 -> (match (_82_2) with
| FStar_Syntax_Syntax.Projector (_82_64) -> begin
true
end
| _82_67 -> begin
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

let def = (let _179_44 = (let _179_43 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_179_43))
in (_179_44)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _82_3 -> (match (_82_3) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _82_76 -> begin
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


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _179_79 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _179_78 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _179_77 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _179_76 = (let _179_75 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _179_74 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _179_73 = (let _179_72 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _179_72))
in (Prims.strcat _179_74 _179_73))))))
in (FStar_All.pipe_right _179_75 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _179_79 _179_78 _179_77 _179_76))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _82_5 -> (match (_82_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _82_105 = (FStar_Syntax_Subst.open_term bs t)
in (match (_82_105) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _82_4 -> (match (_82_4) with
| FStar_Syntax_Syntax.Sig_datacon (d, _82_109, t, l', nparams, _82_114, _82_116, _82_118) when (FStar_Ident.lid_equals l l') -> begin
(

let _82_123 = (FStar_Syntax_Util.arrow_formals t)
in (match (_82_123) with
| (bs', body) -> begin
(

let _82_126 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_82_126) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _82_130 _82_134 -> (match (((_82_130), (_82_134))) with
| ((b', _82_129), (b, _82_133)) -> begin
(let _179_88 = (let _179_87 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_179_87)))
in FStar_Syntax_Syntax.NT (_179_88))
end)) bs_params bs)
in (

let t = (let _179_90 = (let _179_89 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _179_89))
in (FStar_All.pipe_right _179_90 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _82_138 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _82_141 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _179_101 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _179_101))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _179_104 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _179_103 = (let _179_102 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_179_102)))
in ((_179_104), (_179_103))))))))
in (

let extract_one_family = (fun env ind -> (

let _82_156 = (binders_as_mlty_binders env ind.iparams)
in (match (_82_156) with
| (env, vars) -> begin
(

let _82_159 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_82_159) with
| (env, ctors) -> begin
(

let _82_163 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_82_163) with
| (indices, _82_162) -> begin
(

let ml_params = (let _179_113 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _82_165 -> (let _179_112 = (let _179_111 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _179_111))
in ((_179_112), ((Prims.parse_int "0")))))))
in (FStar_List.append vars _179_113))
in (

let tbody = (match ((FStar_Util.find_opt (fun _82_6 -> (match (_82_6) with
| FStar_Syntax_Syntax.RecordType (_82_170) -> begin
true
end
| _82_173 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(

let _82_180 = (FStar_List.hd ctors)
in (match (_82_180) with
| (_82_178, c_ty) -> begin
(

let _82_181 = ()
in (

let fields = (FStar_List.map2 (fun lid ty -> (((lident_as_mlsymbol lid)), (ty))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _82_187 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in ((env), (((false), ((lident_as_mlsymbol ind.iname)), (None), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _82_191, t, _82_194, _82_196, _82_198, _82_200, _82_202))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _82_209, r) -> begin
(

let _82_215 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_82_215) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _82_219, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _82_226 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_82_226) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _82_228 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))


let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (

let l = (fun _82_7 -> (match (_82_7) with
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
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _82_247, t, quals, _82_251) -> begin
(let _179_126 = (FStar_Syntax_Print.lid_to_string lid)
in (let _179_125 = (let _179_124 = (let _179_123 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _179_123))
in (l _179_124))
in (FStar_Util.print2 "\t\t%s @ %s\n" _179_126 _179_125)))
end
| FStar_Syntax_Syntax.Sig_let ((_82_255, (lb)::_82_257), _82_262, _82_264, _82_266) -> begin
(let _179_134 = (let _179_129 = (let _179_128 = (let _179_127 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _179_127.FStar_Syntax_Syntax.fv_name)
in _179_128.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _179_129 FStar_Syntax_Print.lid_to_string))
in (let _179_133 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _179_132 = (let _179_131 = (let _179_130 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _179_130))
in (l _179_131))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _179_134 _179_133 _179_132))))
end
| _82_270 -> begin
(FStar_Util.print_string "other\n")
end)))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _82_276 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (

let _82_274 = (let _179_141 = (let _179_140 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _179_140))
in (FStar_Util.print_string _179_141))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _82_289) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _179_152 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _179_152 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (match ((let _179_155 = (FStar_Syntax_Subst.compress tm)
in _179_155.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _82_305) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let _82_316 = (let _179_156 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _179_156))
in (match (_82_316) with
| (_82_312, tysc, _82_315) -> begin
(let _179_157 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_179_157), (tysc)))
end)))
end
| _82_318 -> begin
(FStar_All.failwith "Not an fv")
end))
in (

let extract_action = (fun g a -> (

let _82_324 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_82_324) with
| (a_tm, ty_sc) -> begin
(

let _82_327 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_82_327) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let _82_336 = (

let _82_330 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_82_330) with
| (return_tm, ty_sc) -> begin
(

let _82_333 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_82_333) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_82_336) with
| (g, return_decl) -> begin
(

let _82_345 = (

let _82_339 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_82_339) with
| (bind_tm, ty_sc) -> begin
(

let _82_342 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_82_342) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_82_345) with
| (g, bind_decl) -> begin
(

let _82_348 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (_82_348) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (_82_350) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _82_354, t, quals, _82_358) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _179_163 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _82_8 -> (match (_82_8) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _82_364 -> begin
false
end))))
in (FStar_All.pipe_right _179_163 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(

let _82_368 = (FStar_Syntax_Util.arrow_formals t)
in (match (_82_368) with
| (bs, _82_367) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (let _179_164 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals _179_164)))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _82_375, _82_377, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _179_165 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g _179_165 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _82_384, quals) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (

let _82_394 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_82_394) with
| (ml_let, _82_391, _82_393) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _82_397, bindings), _82_401) -> begin
(

let _82_433 = (FStar_List.fold_left2 (fun _82_406 ml_lb _82_416 -> (match (((_82_406), (_82_416))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _82_414; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _82_411; FStar_Syntax_Syntax.lbdef = _82_409}) -> begin
(

let lb_lid = (let _179_170 = (let _179_169 = (FStar_Util.right lbname)
in _179_169.FStar_Syntax_Syntax.fv_name)
in _179_170.FStar_Syntax_Syntax.v)
in (

let _82_430 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _82_9 -> (match (_82_9) with
| FStar_Syntax_Syntax.Projector (_82_420) -> begin
true
end
| _82_423 -> begin
false
end)))) then begin
(

let mname = (let _179_172 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _179_172 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _179_174 = (FStar_Util.right lbname)
in (let _179_173 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _179_174 mname _179_173 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let _82_426 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _82_426.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _82_426.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _82_426.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _82_426.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _179_177 = (let _179_176 = (let _179_175 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _179_175 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _179_176))
in ((_179_177), (ml_lb)))
end
in (match (_82_430) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_82_433) with
| (g, ml_lbs') -> begin
(

let flags = (let _179_181 = if (FStar_Util.for_some (fun _82_10 -> (match (_82_10) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _82_437 -> begin
false
end)) quals) then begin
(FStar_Extraction_ML_Syntax.Assumed)::[]
end else begin
[]
end
in (let _179_180 = if (FStar_Util.for_some (fun _82_11 -> (match (_82_11) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _82_441 -> begin
false
end)) quals) then begin
(FStar_Extraction_ML_Syntax.Private)::[]
end else begin
[]
end
in (FStar_List.append _179_181 _179_180)))
in (let _179_184 = (let _179_183 = (let _179_182 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_179_182))
in (_179_183)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), (flags), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_179_184))))
end))
end
| _82_444 -> begin
(let _179_186 = (let _179_185 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _179_185))
in (FStar_All.failwith _179_186))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _82_447, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _179_187 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _179_187 None))
end)
in (let _179_193 = (let _179_192 = (let _179_191 = (let _179_190 = (let _179_189 = (let _179_188 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_179_188))
in {FStar_Syntax_Syntax.lbname = _179_189; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_179_190)::[])
in ((false), (_179_191)))
in ((_179_192), (r), ([]), (quals)))
in FStar_Syntax_Syntax.Sig_let (_179_193)))
in (

let _82_463 = (extract_sig g always_fail)
in (match (_82_463) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _82_12 -> (match (_82_12) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _82_468 -> begin
None
end)))) with
| Some (l) -> begin
(let _179_199 = (let _179_198 = (let _179_195 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_179_195))
in (let _179_197 = (let _179_196 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_179_196)::[])
in (_179_198)::_179_197))
in ((g), (_179_199)))
end
| _82_472 -> begin
(match ((FStar_Util.find_map quals (fun _82_13 -> (match (_82_13) with
| FStar_Syntax_Syntax.Projector (l, _82_476) -> begin
Some (l)
end
| _82_480 -> begin
None
end)))) with
| Some (_82_482) -> begin
((g), ([]))
end
| _82_485 -> begin
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

let _82_495 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_82_495) with
| (ml_main, _82_492, _82_494) -> begin
(let _179_203 = (let _179_202 = (let _179_201 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_179_201))
in (_179_202)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_179_203)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_82_497) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _179_208 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _179_208 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _82_515 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _82_518 = g
in {FStar_Extraction_ML_UEnv.tcenv = _82_518.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _82_518.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _82_518.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _82_522 = (let _179_213 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _179_213))
in (

let _82_526 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_82_526) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end)))
end))))




