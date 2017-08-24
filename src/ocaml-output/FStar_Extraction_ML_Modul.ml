
open Prims
open FStar_Pervasives

let fail_exp = (fun lid t -> (

let uu____15 = (

let uu____18 = (

let uu____19 = (

let uu____29 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
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

let uu____45 = (

let uu____46 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" uu____46))
in ((uu____45), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (uu____42))
in FStar_Syntax_Syntax.Tm_constant (uu____41))
in (FStar_Syntax_Syntax.mk uu____40))
in (uu____37 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____36))
in (uu____35)::[])
in (uu____32)::uu____33))
in ((uu____29), (uu____30))))
in FStar_Syntax_Syntax.Tm_app (uu____19))
in (FStar_Syntax_Syntax.mk uu____18))
in (uu____15 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let as_pair = (fun uu___147_79 -> (match (uu___147_79) with
| (a)::(b)::[] -> begin
((a), (b))
end
| uu____83 -> begin
(failwith "Expected a list with 2 elements")
end))


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____115 -> (match (uu____115) with
| (bv, uu____123) -> begin
(

let uu____124 = (

let uu____125 = (

let uu____127 = (

let uu____128 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____128))
in FStar_Pervasives_Native.Some (uu____127))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____125))
in (

let uu____129 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____124), (uu____129))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def1 = (

let uu____157 = (

let uu____158 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right uu____158 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____157 FStar_Syntax_Util.un_uinst))
in (

let def2 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____160) -> begin
(FStar_Extraction_ML_Term.normalize_abs def1)
end
| uu____175 -> begin
def1
end)
in (

let uu____176 = (match (def2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____183) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____206 -> begin
(([]), (def2))
end)
in (match (uu____176) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___148_218 -> (match (uu___148_218) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____219 -> begin
false
end)) quals)
in (

let uu____220 = (binders_as_mlty_binders env bs)
in (match (uu____220) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____238 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____238 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____241 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___149_243 -> (match (uu___149_243) with
| FStar_Syntax_Syntax.Projector (uu____244) -> begin
true
end
| uu____247 -> begin
false
end))))
in (match (uu____241) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in FStar_Pervasives_Native.Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____250 -> begin
FStar_Pervasives_Native.None
end))
in (

let td = (

let uu____263 = (

let uu____274 = (lident_as_mlsymbol lid)
in ((assumed), (uu____274), (mangled_projector), (ml_bs), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (uu____263)::[])
in (

let def3 = (

let uu____302 = (

let uu____303 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____303))
in (uu____302)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env2 = (

let uu____305 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___150_307 -> (match (uu___150_307) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____308 -> begin
false
end))))
in (match (uu____305) with
| true -> begin
env1
end
| uu____309 -> begin
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

let uu____376 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____377 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____378 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____379 = (

let uu____380 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____385 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____386 = (

let uu____387 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " uu____387))
in (Prims.strcat uu____385 uu____386))))))
in (FStar_All.pipe_right uu____380 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____376 uu____377 uu____378 uu____379))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas) -> begin
(

let uu____425 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____425) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____438, t2, l', nparams, uu____442) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____445 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____445) with
| (bs', body) -> begin
(

let uu____466 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____466) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____502 uu____503 -> (match (((uu____502), (uu____503))) with
| ((b', uu____513), (b, uu____515)) -> begin
(

let uu____520 = (

let uu____525 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____525)))
in FStar_Syntax_Syntax.NT (uu____520))
end)) bs_params bs1)
in (

let t3 = (

let uu____527 = (

let uu____530 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____530))
in (FStar_All.pipe_right uu____527 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____535 -> begin
[]
end))))
in ({iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = se.FStar_Syntax_Syntax.sigquals})::[])
end))
end
| uu____536 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env1 ctor -> (

let mlt = (

let uu____577 = (FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1) uu____577))
in (

let steps = (FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]
in (

let names = (

let uu____582 = (

let uu____583 = (

let uu____586 = (FStar_TypeChecker_Normalize.normalize steps env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp)
in (FStar_Syntax_Subst.compress uu____586))
in uu____583.FStar_Syntax_Syntax.n)
in (match (uu____582) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____589) -> begin
(FStar_List.map (fun uu____602 -> (match (uu____602) with
| ({FStar_Syntax_Syntax.ppname = ppname; FStar_Syntax_Syntax.index = uu____606; FStar_Syntax_Syntax.sort = uu____607}, uu____608) -> begin
ppname.FStar_Ident.idText
end)) bs)
end
| uu____611 -> begin
[]
end))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____622 = (

let uu____623 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (FStar_Pervasives_Native.fst uu____623))
in (

let uu____626 = (

let uu____632 = (lident_as_mlsymbol ctor.dname)
in (

let uu____633 = (

let uu____637 = (FStar_Extraction_ML_Util.argTypes mlt)
in (FStar_List.zip names uu____637))
in ((uu____632), (uu____633))))
in ((uu____622), (uu____626))))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____666 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____666) with
| (env2, vars) -> begin
(

let uu____692 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env2))
in (match (uu____692) with
| (env3, ctors) -> begin
(

let uu____741 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____741) with
| (indices, uu____762) -> begin
(

let ml_params = (

let uu____777 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____792 -> (

let uu____795 = (

let uu____796 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____796))
in ((uu____795), ((Prims.parse_int "0")))))))
in (FStar_List.append vars uu____777))
in (

let tbody = (

let uu____800 = (FStar_Util.find_opt (fun uu___151_802 -> (match (uu___151_802) with
| FStar_Syntax_Syntax.RecordType (uu____803) -> begin
true
end
| uu____808 -> begin
false
end)) ind.iquals)
in (match (uu____800) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____815 = (FStar_List.hd ctors)
in (match (uu____815) with
| (uu____826, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id uu____844 -> (match (uu____844) with
| (uu____849, ty) -> begin
(

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (

let uu____852 = (lident_as_mlsymbol lid)
in ((uu____852), (ty))))
end)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____853 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____855 = (

let uu____866 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____866), (FStar_Pervasives_Native.None), (ml_params), (FStar_Pervasives_Native.Some (tbody))))
in ((env3), (uu____855)))))
end))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____887, t, uu____889, uu____890, uu____891); FStar_Syntax_Syntax.sigrng = uu____892; FStar_Syntax_Syntax.sigquals = uu____893; FStar_Syntax_Syntax.sigmeta = uu____894})::[], uu____895), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____903 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____903) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____930), quals) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let uu____941 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (uu____941) with
| (env1, td) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| uu____993 -> begin
(failwith "Unexpected signature element")
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____1014 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____1014))));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____1018) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1023) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1032) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g1 lid ml_name tm tysc -> (

let uu____1060 = (

let uu____1063 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1063 ml_name tysc false false))
in (match (uu____1060) with
| (g2, mangled_name) -> begin
((

let uu____1069 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g2.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1069) with
| true -> begin
(FStar_Util.print1 "Mangled name: %s\n" (FStar_Pervasives_Native.fst mangled_name))
end
| uu____1070 -> begin
()
end));
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[]))))));
)
end)))
in (

let rec extract_fv = (fun tm -> ((

let uu____1081 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1081) with
| true -> begin
(

let uu____1082 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "extract_fv term: %s\n" uu____1082))
end
| uu____1083 -> begin
()
end));
(

let uu____1084 = (

let uu____1085 = (FStar_Syntax_Subst.compress tm)
in uu____1085.FStar_Syntax_Syntax.n)
in (match (uu____1084) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____1091) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____1102 = (

let uu____1107 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right uu____1107))
in (match (uu____1102) with
| (uu____1136, uu____1137, tysc, uu____1139) -> begin
(

let uu____1140 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____1140), (tysc)))
end)))
end
| uu____1141 -> begin
(failwith "Not an fv")
end));
))
in (

let extract_action = (fun g1 a -> ((

let uu____1157 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1157) with
| true -> begin
(

let uu____1158 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____1159 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.print2 "Action type %s and term %s\n" uu____1158 uu____1159)))
end
| uu____1160 -> begin
()
end));
(

let uu____1161 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____1161) with
| (a_nm, a_lid) -> begin
(

let lbname = (

let uu____1171 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)) FStar_Syntax_Syntax.tun)
in FStar_Util.Inl (uu____1171))
in (

let lb = (FStar_Syntax_Syntax.mk_lb ((lbname), (a.FStar_Syntax_Syntax.action_univs), (FStar_Parser_Const.effect_Tot_lid), (a.FStar_Syntax_Syntax.action_typ), (a.FStar_Syntax_Syntax.action_defn)))
in (

let lbs = ((false), ((lb)::[]))
in (

let action_lb = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool))))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (

let uu____1196 = (FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb)
in (match (uu____1196) with
| (a_let, uu____1203, ty) -> begin
((

let uu____1206 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1206) with
| true -> begin
(

let uu____1207 = (FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let)
in (FStar_Util.print1 "Extracted action term: %s\n" uu____1207))
end
| uu____1208 -> begin
()
end));
(

let uu____1209 = (match (a_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____1214, uu____1215, (mllb)::[]), uu____1217) -> begin
(match (mllb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some (tysc) -> begin
((mllb.FStar_Extraction_ML_Syntax.mllb_def), (tysc))
end
| FStar_Pervasives_Native.None -> begin
(failwith "No type scheme")
end)
end
| uu____1228 -> begin
(failwith "Impossible")
end)
in (match (uu____1209) with
| (exp, tysc) -> begin
((

let uu____1236 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1236) with
| true -> begin
((

let uu____1238 = (FStar_Extraction_ML_Code.string_of_mlty a_nm (FStar_Pervasives_Native.snd tysc))
in (FStar_Util.print1 "Extracted action type: %s\n" uu____1238));
(FStar_List.iter (fun x -> (FStar_Util.print1 "and binders: %s\n" (FStar_Pervasives_Native.fst x))) (FStar_Pervasives_Native.fst tysc));
)
end
| uu____1244 -> begin
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

let uu____1245 = (

let uu____1248 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____1248) with
| (return_tm, ty_sc) -> begin
(

let uu____1256 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____1256) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____1245) with
| (g1, return_decl) -> begin
(

let uu____1268 = (

let uu____1271 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____1271) with
| (bind_tm, ty_sc) -> begin
(

let uu____1279 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____1279) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____1268) with
| (g2, bind_decl) -> begin
(

let uu____1291 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____1291) with
| (g3, actions) -> begin
((g3), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____1303) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1306, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____1310 = (

let uu____1311 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___152_1313 -> (match (uu___152_1313) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1314 -> begin
false
end))))
in (not (uu____1311)))
in (match (uu____1310) with
| true -> begin
((g), ([]))
end
| uu____1319 -> begin
(

let uu____1320 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1320) with
| (bs, uu____1332) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____1344 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit FStar_Pervasives_Native.None)
in (extract_typ_abbrev g fv quals uu____1344)))
end))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____1351, uu____1352) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____1363 = (

let uu____1368 = (FStar_TypeChecker_Env.open_universes_in g.FStar_Extraction_ML_UEnv.tcenv lb.FStar_Syntax_Syntax.lbunivs ((lb.FStar_Syntax_Syntax.lbdef)::(lb.FStar_Syntax_Syntax.lbtyp)::[]))
in (match (uu____1368) with
| (tcenv, uu____1384, def_typ) -> begin
(

let uu____1388 = (as_pair def_typ)
in ((tcenv), (uu____1388)))
end))
in (match (uu____1363) with
| (tcenv, (lbdef, lbtyp)) -> begin
(

let lbtyp1 = (FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp)
in (

let lbdef1 = (FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef lbtyp1)
in (

let uu____1403 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g uu____1403 quals lbdef1))))
end)))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1405, attrs) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (

let uu____1422 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (uu____1422) with
| (ml_let, uu____1430, uu____1431) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, uu____1436, bindings), uu____1438) -> begin
(

let uu____1445 = (FStar_List.fold_left2 (fun uu____1452 ml_lb uu____1454 -> (match (((uu____1452), (uu____1454))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____1467; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1469; FStar_Syntax_Syntax.lbdef = uu____1470}) -> begin
(

let lb_lid = (

let uu____1484 = (

let uu____1489 = (FStar_Util.right lbname)
in uu____1489.FStar_Syntax_Syntax.fv_name)
in uu____1484.FStar_Syntax_Syntax.v)
in (

let uu____1493 = (

let uu____1496 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___153_1498 -> (match (uu___153_1498) with
| FStar_Syntax_Syntax.Projector (uu____1499) -> begin
true
end
| uu____1502 -> begin
false
end))))
in (match (uu____1496) with
| true -> begin
(

let mname = (

let uu____1506 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____1506 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____1507 = (

let uu____1510 = (FStar_Util.right lbname)
in (

let uu____1511 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____1510 mname uu____1511 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____1507) with
| (env1, uu____1515) -> begin
((env1), ((

let uu___158_1516 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((FStar_Pervasives_Native.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = uu___158_1516.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___158_1516.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___158_1516.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = uu___158_1516.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____1518 -> begin
(

let uu____1519 = (

let uu____1520 = (

let uu____1523 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____1523 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1520))
in ((uu____1519), (ml_lb)))
end))
in (match (uu____1493) with
| (g1, ml_lb1) -> begin
((g1), ((ml_lb1)::ml_lbs))
end)))
end)) ((g), ([])) bindings (FStar_Pervasives_Native.snd lbs))
in (match (uu____1445) with
| (g1, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun uu___154_1543 -> (match (uu___154_1543) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____1545 -> begin
FStar_Pervasives_Native.None
end)) quals)
in (

let flags' = (FStar_List.choose (fun uu___155_1550 -> (match (uu___155_1550) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____1555)); FStar_Syntax_Syntax.tk = uu____1556; FStar_Syntax_Syntax.pos = uu____1557; FStar_Syntax_Syntax.vars = uu____1558} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Attribute (s))
end
| uu____1561 -> begin
((FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message");
FStar_Pervasives_Native.None;
)
end)) attrs)
in (

let uu____1565 = (

let uu____1567 = (

let uu____1568 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1568))
in (uu____1567)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in ((g1), (uu____1565)))))
end))
end
| uu____1572 -> begin
(

let uu____1573 = (

let uu____1574 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____1574))
in (failwith uu____1573))
end)
end))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1579, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____1583 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____1583) with
| true -> begin
(

let always_fail = (

let imp = (

let uu____1590 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1590) with
| ([], t1) -> begin
(

let b = (

let uu____1609 = (FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1609))
in (

let uu____1610 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs ((b)::[]) uu____1610 FStar_Pervasives_Native.None)))
end
| (bs, t1) -> begin
(

let uu____1628 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____1628 FStar_Pervasives_Native.None))
end))
in (

let uu___159_1634 = se
in (

let uu____1635 = (

let uu____1636 = (

let uu____1642 = (

let uu____1646 = (

let uu____1648 = (

let uu____1649 = (

let uu____1652 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____1652))
in {FStar_Syntax_Syntax.lbname = uu____1649; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (uu____1648)::[])
in ((false), (uu____1646)))
in ((uu____1642), ([]), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____1636))
in {FStar_Syntax_Syntax.sigel = uu____1635; FStar_Syntax_Syntax.sigrng = uu___159_1634.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___159_1634.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___159_1634.FStar_Syntax_Syntax.sigmeta})))
in (

let uu____1659 = (extract_sig g always_fail)
in (match (uu____1659) with
| (g1, mlm) -> begin
(

let uu____1670 = (FStar_Util.find_map quals (fun uu___156_1672 -> (match (uu___156_1672) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____1675 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____1670) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____1680 = (

let uu____1682 = (

let uu____1683 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1683))
in (

let uu____1684 = (

let uu____1686 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____1686)::[])
in (uu____1682)::uu____1684))
in ((g1), (uu____1680)))
end
| uu____1688 -> begin
(

let uu____1690 = (FStar_Util.find_map quals (fun uu___157_1692 -> (match (uu___157_1692) with
| FStar_Syntax_Syntax.Projector (l, uu____1695) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____1696 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____1690) with
| FStar_Pervasives_Native.Some (uu____1700) -> begin
((g1), ([]))
end
| uu____1702 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____1705 -> begin
((g), ([]))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____1708 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____1708) with
| (ml_main, uu____1716, uu____1717) -> begin
(

let uu____1718 = (

let uu____1720 = (

let uu____1721 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1721))
in (uu____1720)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____1718)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____1723) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_assume (uu____1727) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____1731) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1733) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____1743 -> begin
()
end);
((g), ([]));
)
end);
))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (

let uu____1751 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____1751 FStar_Pervasives_Native.fst)))


let extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____1777 = (FStar_Options.debug_any ())
in (match (uu____1777) with
| true -> begin
(

let uu____1778 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" uu____1778))
end
| uu____1779 -> begin
()
end));
(

let uu____1780 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___160_1783 = g
in {FStar_Extraction_ML_UEnv.tcenv = uu___160_1783.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = uu___160_1783.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___160_1783.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in (

let uu____1784 = (FStar_Util.fold_map extract_sig g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____1784) with
| (g2, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____1801 = (FStar_Options.codegen ())
in (match (uu____1801) with
| FStar_Pervasives_Native.Some ("Kremlin") -> begin
true
end
| uu____1803 -> begin
false
end))
in (

let uu____1805 = (((m.FStar_Syntax_Syntax.name.FStar_Ident.str <> "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface)))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (match (uu____1805) with
| true -> begin
((

let uu____1810 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____1810));
((g2), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (FStar_Pervasives_Native.Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____1840 -> begin
((g2), ([]))
end))))
end)))));
))




