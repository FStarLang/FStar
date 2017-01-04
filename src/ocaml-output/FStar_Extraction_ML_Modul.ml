
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
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _181_9))
in (_181_10)::[])
in (_181_12)::_181_11))
in ((_181_14), (_181_13))))
in FStar_Syntax_Syntax.Tm_app (_181_15))
in (FStar_Syntax_Syntax.mk _181_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _83_24 -> (match (_83_24) with
| (bv, _83_23) -> begin
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
| FStar_Syntax_Syntax.Tm_abs (_83_32) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| _83_35 -> begin
def
end)
in (

let _83_47 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _83_40) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _83_44 -> begin
(([]), (def))
end)
in (match (_83_47) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun _83_1 -> (match (_83_1) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _83_51 -> begin
false
end)) quals)
in (

let _83_55 = (binders_as_mlty_binders env bs)
in (match (_83_55) with
| (env, ml_bs) -> begin
(

let body = (let _181_41 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _181_41 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let mangled_projector = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_2 -> (match (_83_2) with
| FStar_Syntax_Syntax.Projector (_83_59) -> begin
true
end
| _83_62 -> begin
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

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_3 -> (match (_83_3) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _83_71 -> begin
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


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _181_79 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _181_78 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _181_77 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _181_76 = (let _181_75 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _181_74 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _181_73 = (let _181_72 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _181_72))
in (Prims.strcat _181_74 _181_73))))))
in (FStar_All.pipe_right _181_75 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _181_79 _181_78 _181_77 _181_76))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _83_5 -> (match (_83_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _83_100 = (FStar_Syntax_Subst.open_term bs t)
in (match (_83_100) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _83_4 -> (match (_83_4) with
| FStar_Syntax_Syntax.Sig_datacon (d, _83_104, t, l', nparams, _83_109, _83_111, _83_113) when (FStar_Ident.lid_equals l l') -> begin
(

let _83_118 = (FStar_Syntax_Util.arrow_formals t)
in (match (_83_118) with
| (bs', body) -> begin
(

let _83_121 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_83_121) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _83_125 _83_129 -> (match (((_83_125), (_83_129))) with
| ((b', _83_124), (b, _83_128)) -> begin
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
| _83_133 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _83_136 -> begin
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

let _83_151 = (binders_as_mlty_binders env ind.iparams)
in (match (_83_151) with
| (env, vars) -> begin
(

let _83_154 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_83_154) with
| (env, ctors) -> begin
(

let _83_158 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_83_158) with
| (indices, _83_157) -> begin
(

let ml_params = (let _181_113 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _83_160 -> (let _181_112 = (let _181_111 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _181_111))
in ((_181_112), ((Prims.parse_int "0")))))))
in (FStar_List.append vars _181_113))
in (

let tbody = (match ((FStar_Util.find_opt (fun _83_6 -> (match (_83_6) with
| FStar_Syntax_Syntax.RecordType (_83_165) -> begin
true
end
| _83_168 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let _83_177 = (FStar_List.hd ctors)
in (match (_83_177) with
| (_83_175, c_ty) -> begin
(

let _83_178 = ()
in (

let fields = (FStar_List.map2 (fun id ty -> (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (((lident_as_mlsymbol lid)), (ty)))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _83_185 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in ((env), (((false), ((lident_as_mlsymbol ind.iname)), (None), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _83_189, t, _83_192, _83_194, _83_196, _83_198, _83_200))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _83_207, r) -> begin
(

let _83_213 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_83_213) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _83_217, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _83_224 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_83_224) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _83_226 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))


let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (

let l = (fun _83_7 -> (match (_83_7) with
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
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_245, t, quals, _83_249) -> begin
(let _181_126 = (FStar_Syntax_Print.lid_to_string lid)
in (let _181_125 = (let _181_124 = (let _181_123 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _181_123))
in (l _181_124))
in (FStar_Util.print2 "\t\t%s @ %s\n" _181_126 _181_125)))
end
| FStar_Syntax_Syntax.Sig_let ((_83_253, (lb)::_83_255), _83_260, _83_262, _83_264, _83_266) -> begin
(let _181_134 = (let _181_129 = (let _181_128 = (let _181_127 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _181_127.FStar_Syntax_Syntax.fv_name)
in _181_128.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _181_129 FStar_Syntax_Print.lid_to_string))
in (let _181_133 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _181_132 = (let _181_131 = (let _181_130 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _181_130))
in (l _181_131))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _181_134 _181_133 _181_132))))
end
| _83_270 -> begin
(FStar_Util.print_string "other\n")
end)))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _83_276 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (

let _83_274 = (let _181_141 = (let _181_140 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _181_140))
in (FStar_Util.print_string _181_141))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _83_289) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _181_152 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _181_152 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (match ((let _181_155 = (FStar_Syntax_Subst.compress tm)
in _181_155.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _83_305) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let _83_316 = (let _181_156 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _181_156))
in (match (_83_316) with
| (_83_312, tysc, _83_315) -> begin
(let _181_157 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_181_157), (tysc)))
end)))
end
| _83_318 -> begin
(FStar_All.failwith "Not an fv")
end))
in (

let extract_action = (fun g a -> (

let _83_324 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_83_324) with
| (a_tm, ty_sc) -> begin
(

let _83_327 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_83_327) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let _83_336 = (

let _83_330 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_83_330) with
| (return_tm, ty_sc) -> begin
(

let _83_333 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_83_333) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_83_336) with
| (g, return_decl) -> begin
(

let _83_345 = (

let _83_339 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_83_339) with
| (bind_tm, ty_sc) -> begin
(

let _83_342 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_83_342) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_83_345) with
| (g, bind_decl) -> begin
(

let _83_348 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (_83_348) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (_83_350) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_354, t, quals, _83_358) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _181_163 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_8 -> (match (_83_8) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _83_364 -> begin
false
end))))
in (FStar_All.pipe_right _181_163 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(

let _83_368 = (FStar_Syntax_Util.arrow_formals t)
in (match (_83_368) with
| (bs, _83_367) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (let _181_164 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals _181_164)))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _83_375, _83_377, quals, _83_380) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _181_165 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g _181_165 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _83_386, quals, attrs) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (

let _83_397 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_83_397) with
| (ml_let, _83_394, _83_396) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _83_400, bindings), _83_404) -> begin
(

let _83_436 = (FStar_List.fold_left2 (fun _83_409 ml_lb _83_419 -> (match (((_83_409), (_83_419))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _83_417; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _83_414; FStar_Syntax_Syntax.lbdef = _83_412}) -> begin
(

let lb_lid = (let _181_170 = (let _181_169 = (FStar_Util.right lbname)
in _181_169.FStar_Syntax_Syntax.fv_name)
in _181_170.FStar_Syntax_Syntax.v)
in (

let _83_433 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_9 -> (match (_83_9) with
| FStar_Syntax_Syntax.Projector (_83_423) -> begin
true
end
| _83_426 -> begin
false
end)))) then begin
(

let mname = (FStar_All.pipe_right (mangle_projector_lid lb_lid) FStar_Extraction_ML_Syntax.mlpath_of_lident)
in (

let env = (let _181_173 = (FStar_Util.right lbname)
in (let _181_172 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _181_173 mname _181_172 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let _83_429 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _83_429.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _83_429.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _83_429.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _83_429.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _181_176 = (let _181_175 = (let _181_174 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _181_174 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _181_175))
in ((_181_176), (ml_lb)))
end
in (match (_83_433) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_83_436) with
| (g, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun _83_10 -> (match (_83_10) with
| FStar_Syntax_Syntax.Assumption -> begin
Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| _83_442 -> begin
None
end)) quals)
in (

let flags' = (FStar_List.choose (fun _83_11 -> (match (_83_11) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, _83_453)); FStar_Syntax_Syntax.tk = _83_450; FStar_Syntax_Syntax.pos = _83_448; FStar_Syntax_Syntax.vars = _83_446} -> begin
Some (FStar_Extraction_ML_Syntax.Attribute ((FStar_Util.string_of_unicode data)))
end
| _83_459 -> begin
(

let _83_460 = (FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message")
in None)
end)) attrs)
in (let _181_181 = (let _181_180 = (let _181_179 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_181_179))
in (_181_180)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_181_181)))))
end))
end
| _83_464 -> begin
(let _181_183 = (let _181_182 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _181_182))
in (FStar_All.failwith _181_183))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_467, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _181_184 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _181_184 None))
end)
in (let _181_190 = (let _181_189 = (let _181_188 = (let _181_187 = (let _181_186 = (let _181_185 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_181_185))
in {FStar_Syntax_Syntax.lbname = _181_186; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_181_187)::[])
in ((false), (_181_188)))
in ((_181_189), (r), ([]), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_181_190)))
in (

let _83_483 = (extract_sig g always_fail)
in (match (_83_483) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _83_12 -> (match (_83_12) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _83_488 -> begin
None
end)))) with
| Some (l) -> begin
(let _181_196 = (let _181_195 = (let _181_192 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_181_192))
in (let _181_194 = (let _181_193 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_181_193)::[])
in (_181_195)::_181_194))
in ((g), (_181_196)))
end
| _83_492 -> begin
(match ((FStar_Util.find_map quals (fun _83_13 -> (match (_83_13) with
| FStar_Syntax_Syntax.Projector (l, _83_496) -> begin
Some (l)
end
| _83_500 -> begin
None
end)))) with
| Some (_83_502) -> begin
((g), ([]))
end
| _83_505 -> begin
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

let _83_515 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_83_515) with
| (ml_main, _83_512, _83_514) -> begin
(let _181_200 = (let _181_199 = (let _181_198 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_181_198))
in (_181_199)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_181_200)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_83_517) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _181_205 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _181_205 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _83_535 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _83_538 = g
in {FStar_Extraction_ML_UEnv.tcenv = _83_538.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _83_538.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _83_538.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _83_542 = (let _181_210 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _181_210))
in (

let _83_546 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_83_546) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end)))
end))))




