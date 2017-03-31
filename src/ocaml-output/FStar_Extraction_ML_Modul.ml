
open Prims

let fail_exp = (fun lid t -> (

let uu____15 = (

let uu____18 = (

let uu____19 = (

let uu____29 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____30 = (

let uu____32 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____33 = (

let uu____35 = (

let uu____36 = (

let uu____37 = (

let uu____40 = (

let uu____41 = (

let uu____42 = (

let uu____46 = (

let uu____47 = (

let uu____48 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" uu____48))
in (FStar_Bytes.string_as_unicode_bytes uu____47))
in ((uu____46), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (uu____42))
in FStar_Syntax_Syntax.Tm_constant (uu____41))
in (FStar_Syntax_Syntax.mk uu____40))
in (uu____37 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____36))
in (uu____35)::[])
in (uu____32)::uu____33))
in ((uu____29), (uu____30))))
in FStar_Syntax_Syntax.Tm_app (uu____19))
in (FStar_Syntax_Syntax.mk uu____18))
in (uu____15 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____100 -> (match (uu____100) with
| (bv, uu____108) -> begin
(

let uu____109 = (

let uu____110 = (

let uu____112 = (

let uu____113 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____113))
in Some (uu____112))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____110))
in (

let uu____114 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____109), (uu____114))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def1 = (

let uu____142 = (

let uu____143 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right uu____143 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____142 FStar_Syntax_Util.un_uinst))
in (

let def2 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____145) -> begin
(FStar_Extraction_ML_Term.normalize_abs def1)
end
| uu____160 -> begin
def1
end)
in (

let uu____161 = (match (def2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____168) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____191 -> begin
(([]), (def2))
end)
in (match (uu____161) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___149_203 -> (match (uu___149_203) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____204 -> begin
false
end)) quals)
in (

let uu____205 = (binders_as_mlty_binders env bs)
in (match (uu____205) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____223 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____223 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____226 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___150_228 -> (match (uu___150_228) with
| FStar_Syntax_Syntax.Projector (uu____229) -> begin
true
end
| uu____232 -> begin
false
end))))
in (match (uu____226) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____235 -> begin
None
end))
in (

let td = (

let uu____248 = (

let uu____259 = (lident_as_mlsymbol lid)
in ((assumed), (uu____259), (mangled_projector), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (uu____248)::[])
in (

let def3 = (

let uu____287 = (

let uu____288 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____288))
in (uu____287)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env2 = (

let uu____290 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___151_292 -> (match (uu___151_292) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| uu____293 -> begin
false
end))))
in (match (uu____290) with
| true -> begin
env1
end
| uu____294 -> begin
(FStar_Extraction_ML_UEnv.extend_tydef env1 fv td)
end))
in ((env2), (def3)))))))
end)))
end))))))

type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}

type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (

let uu____354 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____355 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____356 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____357 = (

let uu____358 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____363 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____364 = (

let uu____365 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " uu____365))
in (Prims.strcat uu____363 uu____364))))))
in (FStar_All.pipe_right uu____358 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____354 uu____355 uu____356 uu____357))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun uu___153_391 -> (match (uu___153_391) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals1, r) -> begin
(

let uu____407 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____407) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun uu___152_417 -> (match (uu___152_417) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____420, t2, l', nparams, uu____424, uu____425, uu____426) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____431 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____431) with
| (bs', body) -> begin
(

let uu____452 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____452) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____488 uu____489 -> (match (((uu____488), (uu____489))) with
| ((b', uu____499), (b, uu____501)) -> begin
(

let uu____506 = (

let uu____511 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____511)))
in FStar_Syntax_Syntax.NT (uu____506))
end)) bs_params bs1)
in (

let t3 = (

let uu____513 = (

let uu____516 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____516))
in (FStar_All.pipe_right uu____513 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____521 -> begin
[]
end))))
in ({iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = quals1})::[])
end))
end
| uu____522 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env1 ctor -> (

let mlt = (

let uu____559 = (FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1) uu____559))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____570 = (

let uu____571 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (Prims.fst uu____571))
in (

let uu____574 = (

let uu____578 = (lident_as_mlsymbol ctor.dname)
in (

let uu____579 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((uu____578), (uu____579))))
in ((uu____570), (uu____574))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____604 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____604) with
| (env2, vars) -> begin
(

let uu____630 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env2))
in (match (uu____630) with
| (env3, ctors) -> begin
(

let uu____669 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____669) with
| (indices, uu____690) -> begin
(

let ml_params = (

let uu____705 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____720 -> (

let uu____723 = (

let uu____724 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____724))
in ((uu____723), ((Prims.parse_int "0")))))))
in (FStar_List.append vars uu____705))
in (

let tbody = (

let uu____728 = (FStar_Util.find_opt (fun uu___154_730 -> (match (uu___154_730) with
| FStar_Syntax_Syntax.RecordType (uu____731) -> begin
true
end
| uu____736 -> begin
false
end)) ind.iquals)
in (match (uu____728) with
| Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____743 = (FStar_List.hd ctors)
in (match (uu____743) with
| (uu____750, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id ty -> (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (

let uu____764 = (lident_as_mlsymbol lid)
in ((uu____764), (ty))))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____765 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____767 = (

let uu____778 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____778), (None), (ml_params), (Some (tbody))))
in ((env3), (uu____767)))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, uu____798, t, uu____800, uu____801, uu____802, uu____803, uu____804))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], uu____805, r) -> begin
(

let uu____815 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____815) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____837, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let uu____848 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (uu____848) with
| (env1, td) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| uu____900 -> begin
(failwith "Unexpected signature element")
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____918 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____918))));
(match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____926) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g1 lid ml_name tm tysc -> (

let uu____946 = (

let uu____949 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g1 uu____949 ml_name tysc false false))
in (match (uu____946) with
| (g2, mangled_name) -> begin
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[]))))))
end)))
in (

let rec extract_fv = (fun tm -> (

let uu____963 = (

let uu____964 = (FStar_Syntax_Subst.compress tm)
in uu____964.FStar_Syntax_Syntax.n)
in (match (uu____963) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____970) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____981 = (

let uu____986 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right uu____986))
in (match (uu____981) with
| (uu____1015, uu____1016, tysc, uu____1018) -> begin
(

let uu____1019 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____1019), (tysc)))
end)))
end
| uu____1020 -> begin
(failwith "Not an fv")
end)))
in (

let extract_action = (fun g1 a -> (

let uu____1032 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (uu____1032) with
| (a_tm, ty_sc) -> begin
(

let uu____1039 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____1039) with
| (a_nm, a_lid) -> begin
(extend_env g1 a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let uu____1046 = (

let uu____1049 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____1049) with
| (return_tm, ty_sc) -> begin
(

let uu____1057 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____1057) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____1046) with
| (g1, return_decl) -> begin
(

let uu____1069 = (

let uu____1072 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____1072) with
| (bind_tm, ty_sc) -> begin
(

let uu____1080 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____1080) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____1069) with
| (g2, bind_decl) -> begin
(

let uu____1092 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____1092) with
| (g3, actions) -> begin
((g3), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____1104) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1109, t, quals, uu____1112) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____1115 = (

let uu____1116 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___155_1118 -> (match (uu___155_1118) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1119 -> begin
false
end))))
in (FStar_All.pipe_right uu____1116 Prims.op_Negation))
in (match (uu____1115) with
| true -> begin
((g), ([]))
end
| uu____1124 -> begin
(

let uu____1125 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1125) with
| (bs, uu____1137) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____1149 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals uu____1149)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____1156, uu____1157, quals, uu____1159) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____1170 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g uu____1170 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____1173, quals, attrs) -> begin
(

let elet = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool))))) None r)
in (

let uu____1193 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (uu____1193) with
| (ml_let, uu____1201, uu____1202) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, uu____1207, bindings), uu____1209) -> begin
(

let uu____1216 = (FStar_List.fold_left2 (fun uu____1223 ml_lb uu____1225 -> (match (((uu____1223), (uu____1225))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____1238; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1240; FStar_Syntax_Syntax.lbdef = uu____1241}) -> begin
(

let lb_lid = (

let uu____1255 = (

let uu____1260 = (FStar_Util.right lbname)
in uu____1260.FStar_Syntax_Syntax.fv_name)
in uu____1255.FStar_Syntax_Syntax.v)
in (

let uu____1264 = (

let uu____1267 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___156_1269 -> (match (uu___156_1269) with
| FStar_Syntax_Syntax.Projector (uu____1270) -> begin
true
end
| uu____1273 -> begin
false
end))))
in (match (uu____1267) with
| true -> begin
(

let mname = (

let uu____1277 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____1277 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____1278 = (

let uu____1281 = (FStar_Util.right lbname)
in (

let uu____1282 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____1281 mname uu____1282 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____1278) with
| (env1, uu____1286) -> begin
((env1), ((

let uu___161_1287 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = uu___161_1287.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___161_1287.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___161_1287.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = uu___161_1287.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____1289 -> begin
(

let uu____1290 = (

let uu____1291 = (

let uu____1294 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____1294 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst uu____1291))
in ((uu____1290), (ml_lb)))
end))
in (match (uu____1264) with
| (g1, ml_lb1) -> begin
((g1), ((ml_lb1)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (uu____1216) with
| (g1, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun uu___157_1314 -> (match (uu___157_1314) with
| FStar_Syntax_Syntax.Assumption -> begin
Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____1316 -> begin
None
end)) quals)
in (

let flags' = (FStar_List.choose (fun uu___158_1321 -> (match (uu___158_1321) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, uu____1326)); FStar_Syntax_Syntax.tk = uu____1327; FStar_Syntax_Syntax.pos = uu____1328; FStar_Syntax_Syntax.vars = uu____1329} -> begin
Some (FStar_Extraction_ML_Syntax.Attribute ((FStar_Util.string_of_unicode data)))
end
| uu____1334 -> begin
((FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message");
None;
)
end)) attrs)
in (

let uu____1338 = (

let uu____1340 = (

let uu____1341 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1341))
in (uu____1340)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in ((g1), (uu____1338)))))
end))
end
| uu____1345 -> begin
(

let uu____1346 = (

let uu____1347 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____1347))
in (failwith uu____1346))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1352, t, quals, r) -> begin
(

let uu____1358 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____1358) with
| true -> begin
(

let always_fail = (

let imp = (

let uu____1367 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1367) with
| ([], t1) -> begin
(fail_exp lid t1)
end
| (bs, t1) -> begin
(

let uu____1399 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____1399 None))
end))
in (

let uu____1405 = (

let uu____1414 = (

let uu____1418 = (

let uu____1420 = (

let uu____1421 = (

let uu____1424 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (uu____1424))
in {FStar_Syntax_Syntax.lbname = uu____1421; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (uu____1420)::[])
in ((false), (uu____1418)))
in ((uu____1414), (r), ([]), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____1405)))
in (

let uu____1432 = (extract_sig g always_fail)
in (match (uu____1432) with
| (g1, mlm) -> begin
(

let uu____1443 = (FStar_Util.find_map quals (fun uu___159_1445 -> (match (uu___159_1445) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| uu____1448 -> begin
None
end)))
in (match (uu____1443) with
| Some (l) -> begin
(

let uu____1453 = (

let uu____1455 = (

let uu____1456 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1456))
in (

let uu____1457 = (

let uu____1459 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____1459)::[])
in (uu____1455)::uu____1457))
in ((g1), (uu____1453)))
end
| uu____1461 -> begin
(

let uu____1463 = (FStar_Util.find_map quals (fun uu___160_1465 -> (match (uu___160_1465) with
| FStar_Syntax_Syntax.Projector (l, uu____1468) -> begin
Some (l)
end
| uu____1469 -> begin
None
end)))
in (match (uu____1463) with
| Some (uu____1473) -> begin
((g1), ([]))
end
| uu____1475 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____1478 -> begin
((g), ([]))
end))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let uu____1482 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____1482) with
| (ml_main, uu____1490, uu____1491) -> begin
(

let uu____1492 = (

let uu____1494 = (

let uu____1495 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1495))
in (uu____1494)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____1492)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____1497) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p, uu____1508) -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____1510 -> begin
()
end);
((g), ([]));
)
end);
))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (

let uu____1518 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____1518 Prims.fst)))


let extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____1543 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___162_1546 = g
in {FStar_Extraction_ML_UEnv.tcenv = uu___162_1546.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = uu___162_1546.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___162_1546.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in (

let uu____1547 = (FStar_Util.fold_map extract_sig g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____1547) with
| (g2, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____1564 = (FStar_Options.codegen ())
in (match (uu____1564) with
| Some ("Kremlin") -> begin
true
end
| uu____1566 -> begin
false
end))
in (

let uu____1568 = (((m.FStar_Syntax_Syntax.name.FStar_Ident.str <> "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface)))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (match (uu____1568) with
| true -> begin
((

let uu____1573 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____1573));
((g2), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____1603 -> begin
((g2), ([]))
end))))
end)))));
))




