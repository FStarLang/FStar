
open Prims

let fail_exp = (fun lid t -> ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_479 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_478 = (let _0_477 = (FStar_Syntax_Syntax.iarg t)
in (let _0_476 = (let _0_475 = (let _0_474 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ((let _0_473 = (FStar_Bytes.string_as_unicode_bytes (let _0_472 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _0_472)))
in ((_0_473), (FStar_Range.dummyRange))))))) None FStar_Range.dummyRange)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_474))
in (_0_475)::[])
in (_0_477)::_0_476))
in ((_0_479), (_0_478))))))) None FStar_Range.dummyRange))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env uu____70 -> (match (uu____70) with
| (bv, uu____78) -> begin
(let _0_482 = (let _0_480 = Some (FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _0_480))
in (let _0_481 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_0_482), (_0_481))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def = (let _0_484 = (let _0_483 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _0_483 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _0_484 FStar_Syntax_Util.un_uinst))
in (

let def = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____105) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| uu____120 -> begin
def
end)
in (

let uu____121 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____128) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____151 -> begin
(([]), (def))
end)
in (match (uu____121) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___124_163 -> (match (uu___124_163) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____164 -> begin
false
end)) quals)
in (

let uu____165 = (binders_as_mlty_binders env bs)
in (match (uu____165) with
| (env, ml_bs) -> begin
(

let body = (let _0_485 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _0_485 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let mangled_projector = (

let uu____185 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___125_187 -> (match (uu___125_187) with
| FStar_Syntax_Syntax.Projector (uu____188) -> begin
true
end
| uu____191 -> begin
false
end))))
in (match (uu____185) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____194 -> begin
None
end))
in (

let td = (((assumed), ((lident_as_mlsymbol lid)), (mangled_projector), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body)))))::[]
in (

let def = (let _0_486 = FStar_Extraction_ML_Syntax.MLM_Loc ((FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid)))
in (_0_486)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = (

let uu____235 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_237 -> (match (uu___126_237) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| uu____238 -> begin
false
end))))
in (match (uu____235) with
| true -> begin
env
end
| uu____239 -> begin
(FStar_Extraction_ML_UEnv.extend_tydef env fv td)
end))
in ((env), (def)))))))
end)))
end))))))

type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}

type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _0_494 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _0_493 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _0_492 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _0_491 = (let _0_490 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _0_489 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _0_488 = (let _0_487 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _0_487))
in (Prims.strcat _0_489 _0_488))))))
in (FStar_All.pipe_right _0_490 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _0_494 _0_493 _0_492 _0_491))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun uu___128_327 -> (match (uu___128_327) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let uu____343 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____343) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun uu___127_353 -> (match (uu___127_353) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____356, t, l', nparams, uu____360, uu____361, uu____362) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____367 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____367) with
| (bs', body) -> begin
(

let uu____388 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (uu____388) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____424 uu____425 -> (match (((uu____424), (uu____425))) with
| ((b', uu____435), (b, uu____437)) -> begin
FStar_Syntax_Syntax.NT ((let _0_495 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_0_495))))
end)) bs_params bs)
in (

let t = (let _0_497 = (let _0_496 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _0_496))
in (FStar_All.pipe_right _0_497 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| uu____445 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| uu____446 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _0_498 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _0_498))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _0_501 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _0_500 = (let _0_499 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_0_499)))
in ((_0_501), (_0_500))))))))
in (

let extract_one_family = (fun env ind -> (

let uu____516 = (binders_as_mlty_binders env ind.iparams)
in (match (uu____516) with
| (env, vars) -> begin
(

let uu____542 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (uu____542) with
| (env, ctors) -> begin
(

let uu____581 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____581) with
| (indices, uu____602) -> begin
(

let ml_params = (let _0_504 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____630 -> (let _0_503 = (let _0_502 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _0_502))
in ((_0_503), ((Prims.parse_int "0")))))))
in (FStar_List.append vars _0_504))
in (

let tbody = (

let uu____634 = (FStar_Util.find_opt (fun uu___129_636 -> (match (uu___129_636) with
| FStar_Syntax_Syntax.RecordType (uu____637) -> begin
true
end
| uu____642 -> begin
false
end)) ind.iquals)
in (match (uu____634) with
| Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____649 = (FStar_List.hd ctors)
in (match (uu____649) with
| (uu____656, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id ty -> (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (((lident_as_mlsymbol lid)), (ty)))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____670 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in ((env), (((false), ((lident_as_mlsymbol ind.iname)), (None), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, uu____691, t, uu____693, uu____694, uu____695, uu____696, uu____697))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], uu____698, r) -> begin
(

let uu____708 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____708) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____730, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let uu____741 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (uu____741) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| uu____793 -> begin
(failwith "Unexpected signature element")
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (let _0_505 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" _0_505))));
(match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____818) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _0_506 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _0_506 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (

let uu____856 = (FStar_Syntax_Subst.compress tm).FStar_Syntax_Syntax.n
in (match (uu____856) with
| FStar_Syntax_Syntax.Tm_uinst (tm, uu____860) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____871 = (let _0_507 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _0_507))
in (match (uu____871) with
| (uu____892, tysc, uu____894) -> begin
(let _0_508 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_0_508), (tysc)))
end)))
end
| uu____895 -> begin
(failwith "Not an fv")
end)))
in (

let extract_action = (fun g a -> (

let uu____907 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (uu____907) with
| (a_tm, ty_sc) -> begin
(

let uu____914 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____914) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let uu____921 = (

let uu____924 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____924) with
| (return_tm, ty_sc) -> begin
(

let uu____932 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____932) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____921) with
| (g, return_decl) -> begin
(

let uu____944 = (

let uu____947 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____947) with
| (bind_tm, ty_sc) -> begin
(

let uu____955 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____955) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____944) with
| (g, bind_decl) -> begin
(

let uu____967 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (uu____967) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____979) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____984, t, quals, uu____987) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____990 = (let _0_509 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___130_992 -> (match (uu___130_992) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____993 -> begin
false
end))))
in (FStar_All.pipe_right _0_509 Prims.op_Negation))
in (match (uu____990) with
| true -> begin
((g), ([]))
end
| uu____998 -> begin
(

let uu____999 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____999) with
| (bs, uu____1011) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_510 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals _0_510)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____1029, uu____1030, quals, uu____1032) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(let _0_511 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g _0_511 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____1045, quals, attrs) -> begin
(

let elet = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool))))) None r)
in (

let uu____1067 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (uu____1067) with
| (ml_let, uu____1075, uu____1076) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, uu____1081, bindings), uu____1083) -> begin
(

let uu____1090 = (FStar_List.fold_left2 (fun uu____1097 ml_lb uu____1099 -> (match (((uu____1097), (uu____1099))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____1112; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1114; FStar_Syntax_Syntax.lbdef = uu____1115}) -> begin
(

let lb_lid = (FStar_Util.right lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____1133 = (

let uu____1136 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___131_1138 -> (match (uu___131_1138) with
| FStar_Syntax_Syntax.Projector (uu____1139) -> begin
true
end
| uu____1142 -> begin
false
end))))
in (match (uu____1136) with
| true -> begin
(

let mname = (FStar_All.pipe_right (mangle_projector_lid lb_lid) FStar_Extraction_ML_Syntax.mlpath_of_lident)
in (

let env = (let _0_513 = (FStar_Util.right lbname)
in (let _0_512 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _0_513 mname _0_512 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let uu___136_1147 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = uu___136_1147.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___136_1147.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___136_1147.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = uu___136_1147.FStar_Extraction_ML_Syntax.print_typ})))))
end
| uu____1149 -> begin
(let _0_516 = (let _0_515 = (let _0_514 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _0_514 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _0_515))
in ((_0_516), (ml_lb)))
end))
in (match (uu____1133) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (uu____1090) with
| (g, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun uu___132_1169 -> (match (uu___132_1169) with
| FStar_Syntax_Syntax.Assumption -> begin
Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____1171 -> begin
None
end)) quals)
in (

let flags' = (FStar_List.choose (fun uu___133_1176 -> (match (uu___133_1176) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, uu____1181)); FStar_Syntax_Syntax.tk = uu____1182; FStar_Syntax_Syntax.pos = uu____1183; FStar_Syntax_Syntax.vars = uu____1184} -> begin
Some (FStar_Extraction_ML_Syntax.Attribute ((FStar_Util.string_of_unicode data)))
end
| uu____1189 -> begin
((FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message");
None;
)
end)) attrs)
in (let _0_518 = (let _0_517 = FStar_Extraction_ML_Syntax.MLM_Loc ((FStar_Extraction_ML_Util.mlloc_of_range r))
in (_0_517)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_0_518)))))
end))
end
| uu____1196 -> begin
(failwith (let _0_519 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _0_519)))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1201, t, quals, r) -> begin
(

let uu____1207 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____1207) with
| true -> begin
(

let always_fail = (

let imp = (

let uu____1216 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1216) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _0_520 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _0_520 None))
end))
in FStar_Syntax_Syntax.Sig_let ((let _0_524 = (let _0_523 = (let _0_522 = (let _0_521 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None))
in {FStar_Syntax_Syntax.lbname = _0_521; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_0_522)::[])
in ((false), (_0_523)))
in ((_0_524), (r), ([]), (quals), ([])))))
in (

let uu____1260 = (extract_sig g always_fail)
in (match (uu____1260) with
| (g, mlm) -> begin
(

let uu____1271 = (FStar_Util.find_map quals (fun uu___134_1273 -> (match (uu___134_1273) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| uu____1276 -> begin
None
end)))
in (match (uu____1271) with
| Some (l) -> begin
(let _0_528 = (let _0_527 = FStar_Extraction_ML_Syntax.MLM_Loc ((FStar_Extraction_ML_Util.mlloc_of_range r))
in (let _0_526 = (let _0_525 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_0_525)::[])
in (_0_527)::_0_526))
in ((g), (_0_528)))
end
| uu____1282 -> begin
(

let uu____1284 = (FStar_Util.find_map quals (fun uu___135_1286 -> (match (uu___135_1286) with
| FStar_Syntax_Syntax.Projector (l, uu____1289) -> begin
Some (l)
end
| uu____1290 -> begin
None
end)))
in (match (uu____1284) with
| Some (uu____1294) -> begin
((g), ([]))
end
| uu____1296 -> begin
((g), (mlm))
end))
end))
end)))
end
| uu____1299 -> begin
((g), ([]))
end))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let uu____1303 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____1303) with
| (ml_main, uu____1311, uu____1312) -> begin
(let _0_530 = (let _0_529 = FStar_Extraction_ML_Syntax.MLM_Loc ((FStar_Extraction_ML_Util.mlloc_of_range r))
in (_0_529)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_0_530)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____1314) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end);
))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _0_531 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _0_531 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let uu___137_1353 = g
in {FStar_Extraction_ML_UEnv.tcenv = uu___137_1353.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = uu___137_1353.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___137_1353.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in (

let uu____1354 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (uu____1354) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let uu____1370 = (((m.FStar_Syntax_Syntax.name.FStar_Ident.str <> "Prims") && (not (m.FStar_Syntax_Syntax.is_interface))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (match (uu____1370) with
| true -> begin
((let _0_532 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" _0_532));
((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____1404 -> begin
((g), ([]))
end)))
end))));
))




