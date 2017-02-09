
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


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env uu____100 -> (match (uu____100) with
| (bv, uu____108) -> begin
(

let uu____109 = (

let uu____110 = (

let uu____112 = (

let uu____113 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____113))
in Some (uu____112))
in (FStar_Extraction_ML_UEnv.extend_ty env bv uu____110))
in (

let uu____114 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____109), (uu____114))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def = (

let uu____142 = (

let uu____143 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right uu____143 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____142 FStar_Syntax_Util.un_uinst))
in (

let def = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____145) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| uu____160 -> begin
def
end)
in (

let uu____161 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____168) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____191 -> begin
(([]), (def))
end)
in (match (uu____161) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___125_203 -> (match (uu___125_203) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____204 -> begin
false
end)) quals)
in (

let uu____205 = (binders_as_mlty_binders env bs)
in (match (uu____205) with
| (env, ml_bs) -> begin
(

let body = (

let uu____223 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right uu____223 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let mangled_projector = (

let uu____226 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_228 -> (match (uu___126_228) with
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
in ((assumed), (uu____259), (mangled_projector), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body)))))
in (uu____248)::[])
in (

let def = (

let uu____287 = (

let uu____288 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____288))
in (uu____287)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = (

let uu____290 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_292 -> (match (uu___127_292) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| uu____293 -> begin
false
end))))
in (match (uu____290) with
| true -> begin
env
end
| uu____294 -> begin
(FStar_Extraction_ML_UEnv.extend_tydef env fv td)
end))
in ((env), (def)))))))
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


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun uu___129_391 -> (match (uu___129_391) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let uu____407 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____407) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun uu___128_417 -> (match (uu___128_417) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____420, t, l', nparams, uu____424, uu____425, uu____426) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____431 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____431) with
| (bs', body) -> begin
(

let uu____452 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (uu____452) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____488 uu____489 -> (match (((uu____488), (uu____489))) with
| ((b', uu____499), (b, uu____501)) -> begin
(

let uu____506 = (

let uu____511 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____511)))
in FStar_Syntax_Syntax.NT (uu____506))
end)) bs_params bs)
in (

let t = (

let uu____513 = (

let uu____516 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____516))
in (FStar_All.pipe_right uu____513 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| uu____521 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| uu____522 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (

let uu____559 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) uu____559))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____570 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (

let uu____571 = (

let uu____575 = (lident_as_mlsymbol ctor.dname)
in (

let uu____576 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((uu____575), (uu____576))))
in ((uu____570), (uu____571))))))))
in (

let extract_one_family = (fun env ind -> (

let uu____601 = (binders_as_mlty_binders env ind.iparams)
in (match (uu____601) with
| (env, vars) -> begin
(

let uu____627 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (uu____627) with
| (env, ctors) -> begin
(

let uu____666 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____666) with
| (indices, uu____687) -> begin
(

let ml_params = (

let uu____702 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____717 -> (

let uu____720 = (

let uu____721 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____721))
in ((uu____720), ((Prims.parse_int "0")))))))
in (FStar_List.append vars uu____702))
in (

let tbody = (

let uu____725 = (FStar_Util.find_opt (fun uu___130_727 -> (match (uu___130_727) with
| FStar_Syntax_Syntax.RecordType (uu____728) -> begin
true
end
| uu____733 -> begin
false
end)) ind.iquals)
in (match (uu____725) with
| Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____740 = (FStar_List.hd ctors)
in (match (uu____740) with
| (uu____747, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id ty -> (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (

let uu____761 = (lident_as_mlsymbol lid)
in ((uu____761), (ty))))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____762 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____764 = (

let uu____775 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____775), (None), (ml_params), (Some (tbody))))
in ((env), (uu____764)))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, uu____795, t, uu____797, uu____798, uu____799, uu____800, uu____801))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], uu____802, r) -> begin
(

let uu____812 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____812) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____834, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let uu____845 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (uu____845) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| uu____897 -> begin
(failwith "Unexpected signature element")
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____915 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____915))));
(match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____923) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (

let uu____952 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g uu____952 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (

let uu____962 = (

let uu____963 = (FStar_Syntax_Subst.compress tm)
in uu____963.FStar_Syntax_Syntax.n)
in (match (uu____962) with
| FStar_Syntax_Syntax.Tm_uinst (tm, uu____969) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____980 = (

let uu____984 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right uu____984))
in (match (uu____980) with
| (uu____1009, tysc, uu____1011) -> begin
(

let uu____1012 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____1012), (tysc)))
end)))
end
| uu____1013 -> begin
(failwith "Not an fv")
end)))
in (

let extract_action = (fun g a -> (

let uu____1025 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (uu____1025) with
| (a_tm, ty_sc) -> begin
(

let uu____1032 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____1032) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let uu____1039 = (

let uu____1042 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____1042) with
| (return_tm, ty_sc) -> begin
(

let uu____1050 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____1050) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____1039) with
| (g, return_decl) -> begin
(

let uu____1062 = (

let uu____1065 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____1065) with
| (bind_tm, ty_sc) -> begin
(

let uu____1073 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____1073) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____1062) with
| (g, bind_decl) -> begin
(

let uu____1085 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (uu____1085) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____1097) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1102, t, quals, uu____1105) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____1108 = (

let uu____1109 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___131_1111 -> (match (uu___131_1111) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1112 -> begin
false
end))))
in (FStar_All.pipe_right uu____1109 Prims.op_Negation))
in (match (uu____1108) with
| true -> begin
((g), ([]))
end
| uu____1117 -> begin
(

let uu____1118 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1118) with
| (bs, uu____1130) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____1142 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals uu____1142)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____1149, uu____1150, quals, uu____1152) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____1163 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g uu____1163 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____1166, quals, attrs) -> begin
(

let elet = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool))))) None r)
in (

let uu____1186 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (uu____1186) with
| (ml_let, uu____1194, uu____1195) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, uu____1200, bindings), uu____1202) -> begin
(

let uu____1209 = (FStar_List.fold_left2 (fun uu____1216 ml_lb uu____1218 -> (match (((uu____1216), (uu____1218))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____1231; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1233; FStar_Syntax_Syntax.lbdef = uu____1234}) -> begin
(

let lb_lid = (

let uu____1248 = (

let uu____1253 = (FStar_Util.right lbname)
in uu____1253.FStar_Syntax_Syntax.fv_name)
in uu____1248.FStar_Syntax_Syntax.v)
in (

let uu____1257 = (

let uu____1260 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___132_1262 -> (match (uu___132_1262) with
| FStar_Syntax_Syntax.Projector (uu____1263) -> begin
true
end
| uu____1266 -> begin
false
end))))
in (match (uu____1260) with
| true -> begin
(

let mname = (

let uu____1270 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____1270 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (

let uu____1272 = (FStar_Util.right lbname)
in (

let uu____1273 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____1272 mname uu____1273 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let uu___137_1274 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = uu___137_1274.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___137_1274.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___137_1274.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = uu___137_1274.FStar_Extraction_ML_Syntax.print_typ})))))
end
| uu____1276 -> begin
(

let uu____1277 = (

let uu____1278 = (

let uu____1281 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____1281 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst uu____1278))
in ((uu____1277), (ml_lb)))
end))
in (match (uu____1257) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (uu____1209) with
| (g, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun uu___133_1301 -> (match (uu___133_1301) with
| FStar_Syntax_Syntax.Assumption -> begin
Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____1303 -> begin
None
end)) quals)
in (

let flags' = (FStar_List.choose (fun uu___134_1308 -> (match (uu___134_1308) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, uu____1313)); FStar_Syntax_Syntax.tk = uu____1314; FStar_Syntax_Syntax.pos = uu____1315; FStar_Syntax_Syntax.vars = uu____1316} -> begin
Some (FStar_Extraction_ML_Syntax.Attribute ((FStar_Util.string_of_unicode data)))
end
| uu____1321 -> begin
((FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message");
None;
)
end)) attrs)
in (

let uu____1325 = (

let uu____1327 = (

let uu____1328 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1328))
in (uu____1327)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (uu____1325)))))
end))
end
| uu____1332 -> begin
(

let uu____1333 = (

let uu____1334 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____1334))
in (failwith uu____1333))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1339, t, quals, r) -> begin
(

let uu____1345 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____1345) with
| true -> begin
(

let always_fail = (

let imp = (

let uu____1354 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1354) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(

let uu____1386 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs uu____1386 None))
end))
in (

let uu____1392 = (

let uu____1401 = (

let uu____1405 = (

let uu____1407 = (

let uu____1408 = (

let uu____1411 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (uu____1411))
in {FStar_Syntax_Syntax.lbname = uu____1408; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (uu____1407)::[])
in ((false), (uu____1405)))
in ((uu____1401), (r), ([]), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____1392)))
in (

let uu____1419 = (extract_sig g always_fail)
in (match (uu____1419) with
| (g, mlm) -> begin
(

let uu____1430 = (FStar_Util.find_map quals (fun uu___135_1432 -> (match (uu___135_1432) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| uu____1435 -> begin
None
end)))
in (match (uu____1430) with
| Some (l) -> begin
(

let uu____1440 = (

let uu____1442 = (

let uu____1443 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1443))
in (

let uu____1444 = (

let uu____1446 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (uu____1446)::[])
in (uu____1442)::uu____1444))
in ((g), (uu____1440)))
end
| uu____1448 -> begin
(

let uu____1450 = (FStar_Util.find_map quals (fun uu___136_1452 -> (match (uu___136_1452) with
| FStar_Syntax_Syntax.Projector (l, uu____1455) -> begin
Some (l)
end
| uu____1456 -> begin
None
end)))
in (match (uu____1450) with
| Some (uu____1460) -> begin
((g), ([]))
end
| uu____1462 -> begin
((g), (mlm))
end))
end))
end)))
end
| uu____1465 -> begin
((g), ([]))
end))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let uu____1469 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____1469) with
| (ml_main, uu____1477, uu____1478) -> begin
(

let uu____1479 = (

let uu____1481 = (

let uu____1482 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1482))
in (uu____1481)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____1479)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____1484) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p, uu____1495) -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____1497 -> begin
()
end);
((g), ([]));
)
end);
))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (

let uu____1505 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____1505 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____1530 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let uu___138_1533 = g
in {FStar_Extraction_ML_UEnv.tcenv = uu___138_1533.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = uu___138_1533.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___138_1533.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in (

let uu____1534 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (uu____1534) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let uu____1550 = (((m.FStar_Syntax_Syntax.name.FStar_Ident.str <> "Prims") && (not (m.FStar_Syntax_Syntax.is_interface))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (match (uu____1550) with
| true -> begin
((

let uu____1555 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____1555));
((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____1585 -> begin
((g), ([]))
end)))
end)))));
))




