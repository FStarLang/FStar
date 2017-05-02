
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


let as_pair = (fun uu___152_81 -> (match (uu___152_81) with
| (a)::(b)::[] -> begin
((a), (b))
end
| uu____85 -> begin
(failwith "Expected a list with 2 elements")
end))


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____117 -> (match (uu____117) with
| (bv, uu____125) -> begin
(

let uu____126 = (

let uu____127 = (

let uu____129 = (

let uu____130 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____130))
in Some (uu____129))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____127))
in (

let uu____131 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____126), (uu____131))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def1 = (

let uu____159 = (

let uu____160 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right uu____160 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____159 FStar_Syntax_Util.un_uinst))
in (

let def2 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____162) -> begin
(FStar_Extraction_ML_Term.normalize_abs def1)
end
| uu____177 -> begin
def1
end)
in (

let uu____178 = (match (def2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____185) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____208 -> begin
(([]), (def2))
end)
in (match (uu____178) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___153_220 -> (match (uu___153_220) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____221 -> begin
false
end)) quals)
in (

let uu____222 = (binders_as_mlty_binders env bs)
in (match (uu____222) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____240 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____240 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____243 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___154_245 -> (match (uu___154_245) with
| FStar_Syntax_Syntax.Projector (uu____246) -> begin
true
end
| uu____249 -> begin
false
end))))
in (match (uu____243) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____252 -> begin
None
end))
in (

let td = (

let uu____265 = (

let uu____276 = (lident_as_mlsymbol lid)
in ((assumed), (uu____276), (mangled_projector), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (uu____265)::[])
in (

let def3 = (

let uu____304 = (

let uu____305 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____305))
in (uu____304)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env2 = (

let uu____307 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___155_309 -> (match (uu___155_309) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| uu____310 -> begin
false
end))))
in (match (uu____307) with
| true -> begin
env1
end
| uu____311 -> begin
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

let uu____371 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____372 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____373 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____374 = (

let uu____375 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____380 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____381 = (

let uu____382 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " uu____382))
in (Prims.strcat uu____380 uu____381))))))
in (FStar_All.pipe_right uu____375 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____371 uu____372 uu____373 uu____374))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals1) -> begin
(

let uu____423 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____423) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____436, t2, l', nparams, uu____440, uu____441) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____446 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____446) with
| (bs', body) -> begin
(

let uu____467 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____467) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____503 uu____504 -> (match (((uu____503), (uu____504))) with
| ((b', uu____514), (b, uu____516)) -> begin
(

let uu____521 = (

let uu____526 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____526)))
in FStar_Syntax_Syntax.NT (uu____521))
end)) bs_params bs1)
in (

let t3 = (

let uu____528 = (

let uu____531 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____531))
in (FStar_All.pipe_right uu____528 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____536 -> begin
[]
end))))
in ({iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = quals1})::[])
end))
end
| uu____537 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env1 ctor -> (

let mlt = (

let uu____574 = (FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1) uu____574))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____585 = (

let uu____586 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (Prims.fst uu____586))
in (

let uu____589 = (

let uu____593 = (lident_as_mlsymbol ctor.dname)
in (

let uu____594 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((uu____593), (uu____594))))
in ((uu____585), (uu____589))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____619 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____619) with
| (env2, vars) -> begin
(

let uu____645 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env2))
in (match (uu____645) with
| (env3, ctors) -> begin
(

let uu____684 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____684) with
| (indices, uu____705) -> begin
(

let ml_params = (

let uu____720 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____735 -> (

let uu____738 = (

let uu____739 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____739))
in ((uu____738), ((Prims.parse_int "0")))))))
in (FStar_List.append vars uu____720))
in (

let tbody = (

let uu____743 = (FStar_Util.find_opt (fun uu___156_745 -> (match (uu___156_745) with
| FStar_Syntax_Syntax.RecordType (uu____746) -> begin
true
end
| uu____751 -> begin
false
end)) ind.iquals)
in (match (uu____743) with
| Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____758 = (FStar_List.hd ctors)
in (match (uu____758) with
| (uu____765, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id ty -> (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (

let uu____779 = (lident_as_mlsymbol lid)
in ((uu____779), (ty))))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____780 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____782 = (

let uu____793 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____793), (None), (ml_params), (Some (tbody))))
in ((env3), (uu____782)))))
end))
end))
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____813, t, uu____815, uu____816, uu____817, uu____818); FStar_Syntax_Syntax.sigrng = uu____819})::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], uu____820) -> begin
(

let uu____829 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____829) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____851) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let uu____861 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (uu____861) with
| (env1, td) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| uu____913 -> begin
(failwith "Unexpected signature element")
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____931 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____931))));
(match (se.FStar_Syntax_Syntax.sigel) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g1 lid ml_name tm tysc -> (

let uu____958 = (

let uu____961 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g1 uu____961 ml_name tysc false false))
in (match (uu____958) with
| (g2, mangled_name) -> begin
((

let uu____967 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g2.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____967) with
| true -> begin
(FStar_Util.print1 "Mangled name: %s\n" (Prims.fst mangled_name))
end
| uu____968 -> begin
()
end));
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[]))))));
)
end)))
in (

let rec extract_fv = (fun tm -> ((

let uu____979 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____979) with
| true -> begin
(

let uu____980 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "extract_fv term: %s\n" uu____980))
end
| uu____981 -> begin
()
end));
(

let uu____982 = (

let uu____983 = (FStar_Syntax_Subst.compress tm)
in uu____983.FStar_Syntax_Syntax.n)
in (match (uu____982) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____989) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____1000 = (

let uu____1005 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right uu____1005))
in (match (uu____1000) with
| (uu____1034, uu____1035, tysc, uu____1037) -> begin
(

let uu____1038 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____1038), (tysc)))
end)))
end
| uu____1039 -> begin
(failwith "Not an fv")
end));
))
in (

let extract_action = (fun g1 a -> ((

let uu____1055 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1055) with
| true -> begin
(

let uu____1056 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____1057 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.print2 "Action type %s and term %s\n" uu____1056 uu____1057)))
end
| uu____1058 -> begin
()
end));
(

let uu____1059 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____1059) with
| (a_nm, a_lid) -> begin
(

let lbname = (

let uu____1069 = (FStar_Syntax_Syntax.new_bv (Some (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)) FStar_Syntax_Syntax.tun)
in FStar_Util.Inl (uu____1069))
in (

let lb = (FStar_Syntax_Syntax.mk_lb ((lbname), (a.FStar_Syntax_Syntax.action_univs), (FStar_Syntax_Const.effect_Tot_lid), (a.FStar_Syntax_Syntax.action_typ), (a.FStar_Syntax_Syntax.action_defn)))
in (

let lbs = ((false), ((lb)::[]))
in (

let action_lb = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool))))) None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (

let uu____1092 = (FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb)
in (match (uu____1092) with
| (a_let, uu____1099, ty) -> begin
((

let uu____1102 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1102) with
| true -> begin
(

let uu____1103 = (FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let)
in (FStar_Util.print1 "Extracted action term: %s\n" uu____1103))
end
| uu____1104 -> begin
()
end));
(

let uu____1105 = (match (a_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____1110, uu____1111, (mllb)::[]), uu____1113) -> begin
(match (mllb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some (tysc) -> begin
((mllb.FStar_Extraction_ML_Syntax.mllb_def), (tysc))
end
| None -> begin
(failwith "No type scheme")
end)
end
| uu____1124 -> begin
(failwith "Impossible")
end)
in (match (uu____1105) with
| (exp, tysc) -> begin
((

let uu____1132 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1132) with
| true -> begin
((

let uu____1134 = (FStar_Extraction_ML_Code.string_of_mlty a_nm (Prims.snd tysc))
in (FStar_Util.print1 "Extracted action type: %s\n" uu____1134));
(FStar_List.iter (fun x -> (FStar_Util.print1 "and binders: %s\n" (Prims.fst x))) (Prims.fst tysc));
)
end
| uu____1140 -> begin
()
end));
(extend_env g1 a_lid a_nm exp tysc);
)
end));
)
end))))))
end));
))
in (

let uu____1141 = (

let uu____1144 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____1144) with
| (return_tm, ty_sc) -> begin
(

let uu____1152 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____1152) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____1141) with
| (g1, return_decl) -> begin
(

let uu____1164 = (

let uu____1167 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____1167) with
| (bind_tm, ty_sc) -> begin
(

let uu____1175 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____1175) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____1164) with
| (g2, bind_decl) -> begin
(

let uu____1187 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____1187) with
| (g3, actions) -> begin
((g3), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____1199) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1202, t, quals) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____1207 = (

let uu____1208 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___157_1210 -> (match (uu___157_1210) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1211 -> begin
false
end))))
in (not (uu____1208)))
in (match (uu____1207) with
| true -> begin
((g), ([]))
end
| uu____1216 -> begin
(

let uu____1217 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1217) with
| (bs, uu____1229) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____1241 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals uu____1241)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____1248, quals, uu____1250) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____1261 = (

let uu____1266 = (FStar_TypeChecker_Env.open_universes_in g.FStar_Extraction_ML_UEnv.tcenv lb.FStar_Syntax_Syntax.lbunivs ((lb.FStar_Syntax_Syntax.lbdef)::(lb.FStar_Syntax_Syntax.lbtyp)::[]))
in (match (uu____1266) with
| (tcenv, uu____1282, def_typ) -> begin
(

let uu____1286 = (as_pair def_typ)
in ((tcenv), (uu____1286)))
end))
in (match (uu____1261) with
| (tcenv, (lbdef, lbtyp)) -> begin
(

let lbtyp1 = (FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp)
in (

let lbdef1 = (FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef lbtyp1)
in (

let uu____1301 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g uu____1301 quals lbdef1))))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1303, quals, attrs) -> begin
(

let elet = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool))))) None se.FStar_Syntax_Syntax.sigrng)
in (

let uu____1323 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (uu____1323) with
| (ml_let, uu____1331, uu____1332) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, uu____1337, bindings), uu____1339) -> begin
(

let uu____1346 = (FStar_List.fold_left2 (fun uu____1353 ml_lb uu____1355 -> (match (((uu____1353), (uu____1355))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____1368; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1370; FStar_Syntax_Syntax.lbdef = uu____1371}) -> begin
(

let lb_lid = (

let uu____1385 = (

let uu____1390 = (FStar_Util.right lbname)
in uu____1390.FStar_Syntax_Syntax.fv_name)
in uu____1385.FStar_Syntax_Syntax.v)
in (

let uu____1394 = (

let uu____1397 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___158_1399 -> (match (uu___158_1399) with
| FStar_Syntax_Syntax.Projector (uu____1400) -> begin
true
end
| uu____1403 -> begin
false
end))))
in (match (uu____1397) with
| true -> begin
(

let mname = (

let uu____1407 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____1407 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____1408 = (

let uu____1411 = (FStar_Util.right lbname)
in (

let uu____1412 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____1411 mname uu____1412 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____1408) with
| (env1, uu____1416) -> begin
((env1), ((

let uu___163_1417 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = uu___163_1417.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___163_1417.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___163_1417.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = uu___163_1417.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____1419 -> begin
(

let uu____1420 = (

let uu____1421 = (

let uu____1424 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____1424 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst uu____1421))
in ((uu____1420), (ml_lb)))
end))
in (match (uu____1394) with
| (g1, ml_lb1) -> begin
((g1), ((ml_lb1)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (uu____1346) with
| (g1, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun uu___159_1444 -> (match (uu___159_1444) with
| FStar_Syntax_Syntax.Assumption -> begin
Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____1446 -> begin
None
end)) quals)
in (

let flags' = (FStar_List.choose (fun uu___160_1451 -> (match (uu___160_1451) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, uu____1456)); FStar_Syntax_Syntax.tk = uu____1457; FStar_Syntax_Syntax.pos = uu____1458; FStar_Syntax_Syntax.vars = uu____1459} -> begin
Some (FStar_Extraction_ML_Syntax.Attribute ((FStar_Util.string_of_unicode data)))
end
| uu____1464 -> begin
((FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message");
None;
)
end)) attrs)
in (

let uu____1468 = (

let uu____1470 = (

let uu____1471 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1471))
in (uu____1470)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in ((g1), (uu____1468)))))
end))
end
| uu____1475 -> begin
(

let uu____1476 = (

let uu____1477 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____1477))
in (failwith uu____1476))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1482, t, quals) -> begin
(

let uu____1487 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____1487) with
| true -> begin
(

let always_fail = (

let imp = (

let uu____1494 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1494) with
| ([], t1) -> begin
(

let b = (

let uu____1513 = (FStar_Syntax_Syntax.gen_bv "_" None t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1513))
in (

let uu____1514 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs ((b)::[]) uu____1514 None)))
end
| (bs, t1) -> begin
(

let uu____1532 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____1532 None))
end))
in (

let uu___164_1538 = se
in (

let uu____1539 = (

let uu____1540 = (

let uu____1548 = (

let uu____1552 = (

let uu____1554 = (

let uu____1555 = (

let uu____1558 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (uu____1558))
in {FStar_Syntax_Syntax.lbname = uu____1555; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (uu____1554)::[])
in ((false), (uu____1552)))
in ((uu____1548), ([]), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____1540))
in {FStar_Syntax_Syntax.sigel = uu____1539; FStar_Syntax_Syntax.sigrng = uu___164_1538.FStar_Syntax_Syntax.sigrng})))
in (

let uu____1566 = (extract_sig g always_fail)
in (match (uu____1566) with
| (g1, mlm) -> begin
(

let uu____1577 = (FStar_Util.find_map quals (fun uu___161_1579 -> (match (uu___161_1579) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| uu____1582 -> begin
None
end)))
in (match (uu____1577) with
| Some (l) -> begin
(

let uu____1587 = (

let uu____1589 = (

let uu____1590 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1590))
in (

let uu____1591 = (

let uu____1593 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____1593)::[])
in (uu____1589)::uu____1591))
in ((g1), (uu____1587)))
end
| uu____1595 -> begin
(

let uu____1597 = (FStar_Util.find_map quals (fun uu___162_1599 -> (match (uu___162_1599) with
| FStar_Syntax_Syntax.Projector (l, uu____1602) -> begin
Some (l)
end
| uu____1603 -> begin
None
end)))
in (match (uu____1597) with
| Some (uu____1607) -> begin
((g1), ([]))
end
| uu____1609 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____1612 -> begin
((g), ([]))
end))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____1615 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____1615) with
| (ml_main, uu____1623, uu____1624) -> begin
(

let uu____1625 = (

let uu____1627 = (

let uu____1628 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1628))
in (uu____1627)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____1625)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____1630) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____1640 -> begin
()
end);
((g), ([]));
)
end);
))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (

let uu____1648 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____1648 Prims.fst)))


let extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____1674 = (FStar_Options.debug_any ())
in (match (uu____1674) with
| true -> begin
(

let uu____1675 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" uu____1675))
end
| uu____1676 -> begin
()
end));
(

let uu____1677 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___165_1680 = g
in {FStar_Extraction_ML_UEnv.tcenv = uu___165_1680.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = uu___165_1680.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___165_1680.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in (

let uu____1681 = (FStar_Util.fold_map extract_sig g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____1681) with
| (g2, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____1698 = (FStar_Options.codegen ())
in (match (uu____1698) with
| Some ("Kremlin") -> begin
true
end
| uu____1700 -> begin
false
end))
in (

let uu____1702 = (((m.FStar_Syntax_Syntax.name.FStar_Ident.str <> "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface)))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (match (uu____1702) with
| true -> begin
((

let uu____1707 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____1707));
((g2), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____1737 -> begin
((g2), ([]))
end))))
end)))));
))




