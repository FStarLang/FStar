
open Prims
# 34 "FStar.Extraction.ML.Modul.fst"
let fail_exp = (fun lid t -> (let _171_16 = (let _171_15 = (let _171_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _171_13 = (let _171_12 = (FStar_Syntax_Syntax.iarg t)
in (let _171_11 = (let _171_10 = (let _171_9 = (let _171_8 = (let _171_7 = (let _171_6 = (let _171_5 = (let _171_4 = (let _171_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _171_3))
in (FStar_Bytes.string_as_unicode_bytes _171_4))
in ((_171_5), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (_171_6))
in FStar_Syntax_Syntax.Tm_constant (_171_7))
in (FStar_Syntax_Syntax.mk _171_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _171_9))
in (_171_10)::[])
in (_171_12)::_171_11))
in ((_171_14), (_171_13))))
in FStar_Syntax_Syntax.Tm_app (_171_15))
in (FStar_Syntax_Syntax.mk _171_16 None FStar_Range.dummyRange)))

# 42 "FStar.Extraction.ML.Modul.fst"
let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (
# 45 "FStar.Extraction.ML.Modul.fst"
let projecteeName = x.FStar_Ident.ident
in (
# 46 "FStar.Extraction.ML.Modul.fst"
let _79_17 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_79_17) with
| (prefix, constrName) -> begin
(
# 47 "FStar.Extraction.ML.Modul.fst"
let mangledName = (FStar_Ident.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

# 48 "FStar.Extraction.ML.Modul.fst"
let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)

# 50 "FStar.Extraction.ML.Modul.fst"
let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _79_26 -> (match (_79_26) with
| (bv, _79_25) -> begin
(let _171_29 = (let _171_27 = (let _171_26 = (let _171_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_171_25))
in Some (_171_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _171_27))
in (let _171_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_171_29), (_171_28))))
end)) env bs))

# 63 "FStar.Extraction.ML.Modul.fst"
let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env lid quals def -> (
# 67 "FStar.Extraction.ML.Modul.fst"
let def = (let _171_39 = (let _171_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _171_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _171_39 FStar_Syntax_Util.un_uinst))
in (
# 68 "FStar.Extraction.ML.Modul.fst"
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
# 71 "FStar.Extraction.ML.Modul.fst"
let _79_45 = (binders_as_mlty_binders env bs)
in (match (_79_45) with
| (env, ml_bs) -> begin
(
# 72 "FStar.Extraction.ML.Modul.fst"
let body = (let _171_40 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _171_40 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (
# 73 "FStar.Extraction.ML.Modul.fst"
let td = ((((lident_as_mlsymbol lid)), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body)))))::[]
in (
# 74 "FStar.Extraction.ML.Modul.fst"
let def = (let _171_42 = (let _171_41 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_171_41))
in (_171_42)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (
# 75 "FStar.Extraction.ML.Modul.fst"
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

# 78 "FStar.Extraction.ML.Modul.fst"
type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}

# 84 "FStar.Extraction.ML.Modul.fst"
let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))

# 87 "FStar.Extraction.ML.Modul.fst"
type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}

# 89 "FStar.Extraction.ML.Modul.fst"
let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))

# 95 "FStar.Extraction.ML.Modul.fst"
let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _171_77 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _171_76 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _171_75 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _171_74 = (let _171_73 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _171_72 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _171_71 = (let _171_70 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _171_70))
in (Prims.strcat _171_72 _171_71))))))
in (FStar_All.pipe_right _171_73 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _171_77 _171_76 _171_75 _171_74))))))

# 102 "FStar.Extraction.ML.Modul.fst"
let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _79_3 -> (match (_79_3) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(
# 108 "FStar.Extraction.ML.Modul.fst"
let _79_82 = (FStar_Syntax_Subst.open_term bs t)
in (match (_79_82) with
| (bs, t) -> begin
(
# 109 "FStar.Extraction.ML.Modul.fst"
let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _79_2 -> (match (_79_2) with
| FStar_Syntax_Syntax.Sig_datacon (d, _79_86, t, l', nparams, _79_91, _79_93, _79_95) when (FStar_Ident.lid_equals l l') -> begin
(
# 111 "FStar.Extraction.ML.Modul.fst"
let _79_100 = (FStar_Syntax_Util.arrow_formals t)
in (match (_79_100) with
| (bs', body) -> begin
(
# 112 "FStar.Extraction.ML.Modul.fst"
let _79_103 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_79_103) with
| (bs_params, rest) -> begin
(
# 113 "FStar.Extraction.ML.Modul.fst"
let subst = (FStar_List.map2 (fun _79_107 _79_111 -> (match (((_79_107), (_79_111))) with
| ((b', _79_106), (b, _79_110)) -> begin
(let _171_86 = (let _171_85 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_171_85)))
in FStar_Syntax_Syntax.NT (_171_86))
end)) bs_params bs)
in (
# 114 "FStar.Extraction.ML.Modul.fst"
let t = (let _171_88 = (let _171_87 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _171_87))
in (FStar_All.pipe_right _171_88 (FStar_Syntax_Subst.subst subst)))
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

# 123 "FStar.Extraction.ML.Modul.fst"
type env_t =
FStar_Extraction_ML_UEnv.env

# 125 "FStar.Extraction.ML.Modul.fst"
let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (
# 128 "FStar.Extraction.ML.Modul.fst"
let extract_ctor = (fun ml_tyvars env ctor -> (
# 129 "FStar.Extraction.ML.Modul.fst"
let mlt = (let _171_99 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _171_99))
in (
# 130 "FStar.Extraction.ML.Modul.fst"
let tys = ((ml_tyvars), (mlt))
in (
# 131 "FStar.Extraction.ML.Modul.fst"
let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _171_102 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _171_101 = (let _171_100 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_171_100)))
in ((_171_102), (_171_101))))))))
in (
# 135 "FStar.Extraction.ML.Modul.fst"
let extract_one_family = (fun env ind -> (
# 136 "FStar.Extraction.ML.Modul.fst"
let _79_133 = (binders_as_mlty_binders env ind.iparams)
in (match (_79_133) with
| (env, vars) -> begin
(
# 137 "FStar.Extraction.ML.Modul.fst"
let _79_136 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_79_136) with
| (env, ctors) -> begin
(
# 138 "FStar.Extraction.ML.Modul.fst"
let _79_140 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_79_140) with
| (indices, _79_139) -> begin
(
# 139 "FStar.Extraction.ML.Modul.fst"
let ml_params = (let _171_111 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _79_142 -> (let _171_110 = (let _171_109 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _171_109))
in ((_171_110), (0))))))
in (FStar_List.append vars _171_111))
in (
# 140 "FStar.Extraction.ML.Modul.fst"
let tbody = (match ((FStar_Util.find_opt (fun _79_4 -> (match (_79_4) with
| FStar_Syntax_Syntax.RecordType (_79_147) -> begin
true
end
| _79_150 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(
# 142 "FStar.Extraction.ML.Modul.fst"
let _79_157 = (FStar_List.hd ctors)
in (match (_79_157) with
| (_79_155, c_ty) -> begin
(
# 143 "FStar.Extraction.ML.Modul.fst"
let _79_158 = ()
in (
# 144 "FStar.Extraction.ML.Modul.fst"
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
# 153 "FStar.Extraction.ML.Modul.fst"
let _79_192 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_79_192) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _79_196, r) -> begin
(
# 157 "FStar.Extraction.ML.Modul.fst"
let ifams = (bundle_as_inductive_families env ses quals)
in (
# 159 "FStar.Extraction.ML.Modul.fst"
let _79_203 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_79_203) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _79_205 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))

# 162 "FStar.Extraction.ML.Modul.fst"
let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (
# 169 "FStar.Extraction.ML.Modul.fst"
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
(let _171_124 = (FStar_Syntax_Print.lid_to_string lid)
in (let _171_123 = (let _171_122 = (let _171_121 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _171_121))
in (l _171_122))
in (FStar_Util.print2 "\t\t%s @ %s\n" _171_124 _171_123)))
end
| FStar_Syntax_Syntax.Sig_let ((_79_232, (lb)::_79_234), _79_239, _79_241, _79_243) -> begin
(let _171_132 = (let _171_127 = (let _171_126 = (let _171_125 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _171_125.FStar_Syntax_Syntax.fv_name)
in _171_126.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _171_127 FStar_Syntax_Print.lid_to_string))
in (let _171_131 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _171_130 = (let _171_129 = (let _171_128 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _171_128))
in (l _171_129))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _171_132 _171_131 _171_130))))
end
| _79_247 -> begin
(FStar_Util.print_string "other\n")
end)))

# 187 "FStar.Extraction.ML.Modul.fst"
let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (
# 191 "FStar.Extraction.ML.Modul.fst"
let _79_253 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (
# 192 "FStar.Extraction.ML.Modul.fst"
let _79_251 = (let _171_139 = (let _171_138 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _171_138))
in (FStar_Util.print_string _171_139))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _79_266) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(
# 201 "FStar.Extraction.ML.Modul.fst"
let extend_env = (fun g lid ml_name tm tysc -> (
# 202 "FStar.Extraction.ML.Modul.fst"
let mangled_name = (Prims.snd ml_name)
in (
# 203 "FStar.Extraction.ML.Modul.fst"
let g = (let _171_150 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _171_150 ml_name tysc false false))
in (
# 204 "FStar.Extraction.ML.Modul.fst"
let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), (0)); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NoLetQualifier), ((lb)::[])))))))))
in (
# 213 "FStar.Extraction.ML.Modul.fst"
let rec extract_fv = (fun tm -> (match ((let _171_153 = (FStar_Syntax_Subst.compress tm)
in _171_153.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _79_282) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 216 "FStar.Extraction.ML.Modul.fst"
let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (
# 217 "FStar.Extraction.ML.Modul.fst"
let _79_293 = (let _171_154 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _171_154))
in (match (_79_293) with
| (_79_289, tysc, _79_292) -> begin
(let _171_155 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_171_155), (tysc)))
end)))
end
| _79_295 -> begin
(FStar_All.failwith "Not an fv")
end))
in (
# 221 "FStar.Extraction.ML.Modul.fst"
let extract_action = (fun g a -> (
# 222 "FStar.Extraction.ML.Modul.fst"
let _79_301 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_79_301) with
| (a_tm, ty_sc) -> begin
(
# 223 "FStar.Extraction.ML.Modul.fst"
let _79_304 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_79_304) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (
# 226 "FStar.Extraction.ML.Modul.fst"
let _79_313 = (
# 227 "FStar.Extraction.ML.Modul.fst"
let _79_307 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_79_307) with
| (return_tm, ty_sc) -> begin
(
# 228 "FStar.Extraction.ML.Modul.fst"
let _79_310 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_79_310) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_79_313) with
| (g, return_decl) -> begin
(
# 231 "FStar.Extraction.ML.Modul.fst"
let _79_322 = (
# 232 "FStar.Extraction.ML.Modul.fst"
let _79_316 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_79_316) with
| (bind_tm, ty_sc) -> begin
(
# 233 "FStar.Extraction.ML.Modul.fst"
let _79_319 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_79_319) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_79_322) with
| (g, bind_decl) -> begin
(
# 236 "FStar.Extraction.ML.Modul.fst"
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
if (let _171_161 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_6 -> (match (_79_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _79_341 -> begin
false
end))))
in (FStar_All.pipe_right _171_161 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(
# 246 "FStar.Extraction.ML.Modul.fst"
let _79_345 = (FStar_Syntax_Util.arrow_formals t)
in (match (_79_345) with
| (bs, _79_344) -> begin
(let _171_162 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g lid quals _171_162))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _79_351, _79_353, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _171_165 = (let _171_164 = (let _171_163 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _171_163.FStar_Syntax_Syntax.fv_name)
in _171_164.FStar_Syntax_Syntax.v)
in (extract_typ_abbrev g _171_165 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _79_360, quals) -> begin
(
# 253 "FStar.Extraction.ML.Modul.fst"
let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (
# 254 "FStar.Extraction.ML.Modul.fst"
let _79_370 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_79_370) with
| (ml_let, _79_367, _79_369) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _79_373) -> begin
(
# 257 "FStar.Extraction.ML.Modul.fst"
let _79_405 = (FStar_List.fold_left2 (fun _79_378 ml_lb _79_388 -> (match (((_79_378), (_79_388))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _79_386; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _79_383; FStar_Syntax_Syntax.lbdef = _79_381}) -> begin
(
# 259 "FStar.Extraction.ML.Modul.fst"
let lb_lid = (let _171_170 = (let _171_169 = (FStar_Util.right lbname)
in _171_169.FStar_Syntax_Syntax.fv_name)
in _171_170.FStar_Syntax_Syntax.v)
in (
# 260 "FStar.Extraction.ML.Modul.fst"
let _79_402 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_7 -> (match (_79_7) with
| FStar_Syntax_Syntax.Projector (_79_392) -> begin
true
end
| _79_395 -> begin
false
end)))) then begin
(
# 262 "FStar.Extraction.ML.Modul.fst"
let mname = (let _171_172 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _171_172 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (
# 263 "FStar.Extraction.ML.Modul.fst"
let env = (let _171_174 = (FStar_Util.right lbname)
in (let _171_173 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _171_174 mname _171_173 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((
# 264 "FStar.Extraction.ML.Modul.fst"
let _79_398 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), (0)); FStar_Extraction_ML_Syntax.mllb_tysc = _79_398.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _79_398.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _79_398.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _79_398.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _171_177 = (let _171_176 = (let _171_175 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _171_175 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _171_176))
in ((_171_177), (ml_lb)))
end
in (match (_79_402) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_79_405) with
| (g, ml_lbs') -> begin
(
# 268 "FStar.Extraction.ML.Modul.fst"
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
in (let _171_181 = (let _171_180 = (let _171_179 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_171_179))
in (_171_180)::(FStar_Extraction_ML_Syntax.MLM_Let (((qual), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_171_181))))
end))
end
| _79_412 -> begin
(let _171_183 = (let _171_182 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _171_182))
in (FStar_All.failwith _171_183))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _79_415, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(
# 282 "FStar.Extraction.ML.Modul.fst"
let always_fail = (
# 283 "FStar.Extraction.ML.Modul.fst"
let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _171_184 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _171_184 None))
end)
in (let _171_190 = (let _171_189 = (let _171_188 = (let _171_187 = (let _171_186 = (let _171_185 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_171_185))
in {FStar_Syntax_Syntax.lbname = _171_186; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_171_187)::[])
in ((false), (_171_188)))
in ((_171_189), (r), ([]), (quals)))
in FStar_Syntax_Syntax.Sig_let (_171_190)))
in (
# 291 "FStar.Extraction.ML.Modul.fst"
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
(let _171_196 = (let _171_195 = (let _171_192 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_171_192))
in (let _171_194 = (let _171_193 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_171_193)::[])
in (_171_195)::_171_194))
in ((g), (_171_196)))
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
# 306 "FStar.Extraction.ML.Modul.fst"
let _79_463 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_79_463) with
| (ml_main, _79_460, _79_462) -> begin
(let _171_200 = (let _171_199 = (let _171_198 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_171_198))
in (_171_199)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_171_200)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_79_465) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))

# 316 "FStar.Extraction.ML.Modul.fst"
let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _171_205 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _171_205 Prims.fst)))

# 318 "FStar.Extraction.ML.Modul.fst"
let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (
# 321 "FStar.Extraction.ML.Modul.fst"
let _79_483 = (FStar_Syntax_Syntax.reset_gensym ())
in (
# 322 "FStar.Extraction.ML.Modul.fst"
let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (
# 323 "FStar.Extraction.ML.Modul.fst"
let g = (
# 323 "FStar.Extraction.ML.Modul.fst"
let _79_486 = g
in {FStar_Extraction_ML_UEnv.tcenv = _79_486.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _79_486.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _79_486.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(
# 327 "FStar.Extraction.ML.Modul.fst"
let g = (extract_iface g m)
in ((g), ([])))
end else begin
(
# 329 "FStar.Extraction.ML.Modul.fst"
let _79_490 = (let _171_210 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _171_210))
in (
# 330 "FStar.Extraction.ML.Modul.fst"
let _79_494 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_79_494) with
| (g, sigs) -> begin
(
# 331 "FStar.Extraction.ML.Modul.fst"
let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end)))
end))))




