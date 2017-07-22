
open Prims
open FStar_Pervasives

let fail_exp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun lid t -> (

let uu____11 = (

let uu____14 = (

let uu____15 = (

let uu____30 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____31 = (

let uu____34 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____35 = (

let uu____38 = (

let uu____39 = (

let uu____40 = (

let uu____43 = (

let uu____44 = (

let uu____45 = (

let uu____52 = (

let uu____53 = (

let uu____54 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" uu____54))
in (FStar_Bytes.string_as_unicode_bytes uu____53))
in ((uu____52), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (uu____45))
in FStar_Syntax_Syntax.Tm_constant (uu____44))
in (FStar_Syntax_Syntax.mk uu____43))
in (uu____40 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39))
in (uu____38)::[])
in (uu____34)::uu____35))
in ((uu____30), (uu____31))))
in FStar_Syntax_Syntax.Tm_app (uu____15))
in (FStar_Syntax_Syntax.mk uu____14))
in (uu____11 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let as_pair : 'Auu____75 . 'Auu____75 Prims.list  ->  ('Auu____75 * 'Auu____75) = (fun uu___148_85 -> (match (uu___148_85) with
| (a)::(b)::[] -> begin
((a), (b))
end
| uu____90 -> begin
(failwith "Expected a list with 2 elements")
end))


let rec extract_attr : FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.tyattr FStar_Pervasives_Native.option = (fun x -> (

let uu____103 = (FStar_Syntax_Subst.compress x)
in (match (uu____103) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____107; FStar_Syntax_Syntax.vars = uu____108} when (

let uu____111 = (

let uu____112 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____112))
in (uu____111 = "FStar.Pervasives.PpxDerivingShow")) -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.PpxDerivingShow)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____114; FStar_Syntax_Syntax.vars = uu____115}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, uu____117)); FStar_Syntax_Syntax.pos = uu____118; FStar_Syntax_Syntax.vars = uu____119}, uu____120))::[]); FStar_Syntax_Syntax.pos = uu____121; FStar_Syntax_Syntax.vars = uu____122} when (

let uu____157 = (

let uu____158 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____158))
in (uu____157 = "FStar.Pervasives.PpxDerivingShowConstant")) -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant ((FStar_Util.string_of_unicode data)))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____160); FStar_Syntax_Syntax.pos = uu____161; FStar_Syntax_Syntax.vars = uu____162} -> begin
(extract_attr x1)
end
| a -> begin
FStar_Pervasives_Native.None
end)))


let extract_attrs : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Extraction_ML_Syntax.tyattr Prims.list = (fun attrs -> (FStar_List.choose extract_attr attrs))


let binders_as_mlty_binders : 'Auu____186 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____186) Prims.list  ->  (FStar_Extraction_ML_UEnv.env * (Prims.string * Prims.int) Prims.list) = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____232 -> (match (uu____232) with
| (bv, uu____246) -> begin
(

let uu____247 = (

let uu____248 = (

let uu____251 = (

let uu____252 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____252))
in FStar_Pervasives_Native.Some (uu____251))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____248))
in (

let uu____253 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____247), (uu____253))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals attrs def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def1 = (

let uu____298 = (

let uu____299 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right uu____299 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____298 FStar_Syntax_Util.un_uinst))
in (

let def2 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____301) -> begin
(FStar_Extraction_ML_Term.normalize_abs def1)
end
| uu____318 -> begin
def1
end)
in (

let uu____319 = (match (def2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____330) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____351 -> begin
(([]), (def2))
end)
in (match (uu____319) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___149_372 -> (match (uu___149_372) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____373 -> begin
false
end)) quals)
in (

let uu____374 = (binders_as_mlty_binders env bs)
in (match (uu____374) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____406 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____406 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____410 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___150_415 -> (match (uu___150_415) with
| FStar_Syntax_Syntax.Projector (uu____416) -> begin
true
end
| uu____421 -> begin
false
end))))
in (match (uu____410) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in FStar_Pervasives_Native.Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____425 -> begin
FStar_Pervasives_Native.None
end))
in (

let attrs1 = (extract_attrs attrs)
in (

let td = (

let uu____456 = (

let uu____481 = (lident_as_mlsymbol lid)
in ((assumed), (uu____481), (mangled_projector), (ml_bs), (attrs1), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (uu____456)::[])
in (

let def3 = (

let uu____545 = (

let uu____546 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____546))
in (uu____545)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env2 = (

let uu____548 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___151_552 -> (match (uu___151_552) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____553 -> begin
false
end))))
in (match (uu____548) with
| true -> begin
(FStar_Extraction_ML_UEnv.extend_type_name env1 fv)
end
| uu____554 -> begin
(FStar_Extraction_ML_UEnv.extend_tydef env1 fv td)
end))
in ((env2), (def3))))))))
end)))
end))))))

type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}


let __proj__Mkdata_constructor__item__dname : data_constructor  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {dname = __fname__dname; dtyp = __fname__dtyp} -> begin
__fname__dname
end))


let __proj__Mkdata_constructor__item__dtyp : data_constructor  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {dname = __fname__dname; dtyp = __fname__dtyp} -> begin
__fname__dtyp
end))

type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list; iattrs : FStar_Extraction_ML_Syntax.tyattrs}


let __proj__Mkinductive_family__item__iname : inductive_family  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; iattrs = __fname__iattrs} -> begin
__fname__iname
end))


let __proj__Mkinductive_family__item__iparams : inductive_family  ->  FStar_Syntax_Syntax.binders = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; iattrs = __fname__iattrs} -> begin
__fname__iparams
end))


let __proj__Mkinductive_family__item__ityp : inductive_family  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; iattrs = __fname__iattrs} -> begin
__fname__ityp
end))


let __proj__Mkinductive_family__item__idatas : inductive_family  ->  data_constructor Prims.list = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; iattrs = __fname__iattrs} -> begin
__fname__idatas
end))


let __proj__Mkinductive_family__item__iquals : inductive_family  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; iattrs = __fname__iattrs} -> begin
__fname__iquals
end))


let __proj__Mkinductive_family__item__iattrs : inductive_family  ->  FStar_Extraction_ML_Syntax.tyattrs = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; iattrs = __fname__iattrs} -> begin
__fname__iattrs
end))


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (

let uu____701 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____702 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____703 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____704 = (

let uu____705 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____716 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____717 = (

let uu____718 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " uu____718))
in (Prims.strcat uu____716 uu____717))))))
in (FStar_All.pipe_right uu____705 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____701 uu____702 uu____703 uu____704))))))


let bundle_as_inductive_families : 'Auu____731 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____731  ->  FStar_Syntax_Syntax.attribute Prims.list  ->  (FStar_Extraction_ML_UEnv.env * inductive_family Prims.list) = (fun env ses quals attrs -> (

let uu____762 = (FStar_Util.fold_map (fun env1 se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas) -> begin
(

let uu____809 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____809) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____848, t2, l', nparams, uu____852) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____857 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____857) with
| (bs', body) -> begin
(

let uu____890 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____890) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____961 uu____962 -> (match (((uu____961), (uu____962))) with
| ((b', uu____980), (b, uu____982)) -> begin
(

let uu____991 = (

let uu____998 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____998)))
in FStar_Syntax_Syntax.NT (uu____991))
end)) bs_params bs1)
in (

let t3 = (

let uu____1000 = (

let uu____1003 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____1003))
in (FStar_All.pipe_right uu____1000 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____1008 -> begin
[]
end))))
in (

let attrs1 = (extract_attrs (FStar_List.append se.FStar_Syntax_Syntax.sigattrs attrs))
in (

let env2 = (

let uu____1013 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.extend_type_name env1 uu____1013))
in ((env2), (({iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = se.FStar_Syntax_Syntax.sigquals; iattrs = attrs1})::[])))))
end))
end
| uu____1016 -> begin
((env1), ([]))
end)) env ses)
in (match (uu____762) with
| (env1, ifams) -> begin
((env1), ((FStar_List.flatten ifams)))
end)))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env1 ctor -> (

let mlt = (

let uu____1102 = (FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1102))
in (

let steps = (FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]
in (

let names1 = (

let uu____1109 = (

let uu____1110 = (

let uu____1113 = (FStar_TypeChecker_Normalize.normalize steps env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp)
in (FStar_Syntax_Subst.compress uu____1113))
in uu____1110.FStar_Syntax_Syntax.n)
in (match (uu____1109) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____1117) -> begin
(FStar_List.map (fun uu____1143 -> (match (uu____1143) with
| ({FStar_Syntax_Syntax.ppname = ppname; FStar_Syntax_Syntax.index = uu____1149; FStar_Syntax_Syntax.sort = uu____1150}, uu____1151) -> begin
ppname.FStar_Ident.idText
end)) bs)
end
| uu____1154 -> begin
[]
end))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____1173 = (

let uu____1174 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (FStar_Pervasives_Native.fst uu____1174))
in (

let uu____1179 = (

let uu____1190 = (lident_as_mlsymbol ctor.dname)
in (

let uu____1191 = (

let uu____1198 = (FStar_Extraction_ML_Util.argTypes mlt)
in (FStar_List.zip names1 uu____1198))
in ((uu____1190), (uu____1191))))
in ((uu____1173), (uu____1179))))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____1250 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____1250) with
| (env2, vars) -> begin
(

let uu____1301 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env2))
in (match (uu____1301) with
| (env3, ctors) -> begin
(

let uu____1398 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____1398) with
| (indices, uu____1438) -> begin
(

let ml_params = (

let uu____1462 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____1493 -> (

let uu____1498 = (

let uu____1499 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____1499))
in ((uu____1498), ((Prims.parse_int "0")))))))
in (FStar_List.append vars uu____1462))
in (

let tbody = (

let uu____1505 = (FStar_Util.find_opt (fun uu___152_1510 -> (match (uu___152_1510) with
| FStar_Syntax_Syntax.RecordType (uu____1511) -> begin
true
end
| uu____1520 -> begin
false
end)) ind.iquals)
in (match (uu____1505) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____1531 = (FStar_List.hd ctors)
in (match (uu____1531) with
| (uu____1552, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id uu____1591 -> (match (uu____1591) with
| (uu____1600, ty) -> begin
(

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
in (

let uu____1603 = (lident_as_mlsymbol lid)
in ((uu____1603), (ty))))
end)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____1604 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____1607 = (

let uu____1630 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____1630), (FStar_Pervasives_Native.None), (ml_params), (ind.iattrs), (FStar_Pervasives_Native.Some (tbody))))
in ((env3), (uu____1607)))))
end))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____1672, t, uu____1674, uu____1675, uu____1676); FStar_Syntax_Syntax.sigrng = uu____1677; FStar_Syntax_Syntax.sigquals = uu____1678; FStar_Syntax_Syntax.sigmeta = uu____1679; FStar_Syntax_Syntax.sigattrs = uu____1680})::[], uu____1681), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____1698 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____1698) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____1748), quals) -> begin
(

let uu____1762 = (bundle_as_inductive_families env ses quals se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____1762) with
| (env1, ifams) -> begin
(

let uu____1783 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____1783) with
| (env2, td) -> begin
((env2), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end))
end))
end
| uu____1892 -> begin
(failwith "Unexpected signature element")
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____1929 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____1929))));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____1936) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1945) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1962) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g1 lid ml_name tm tysc -> (

let uu____2000 = (

let uu____2005 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2005 ml_name tysc false false))
in (match (uu____2000) with
| (g2, mangled_name) -> begin
((

let uu____2013 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g2.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2013) with
| true -> begin
(FStar_Util.print1 "Mangled name: %s\n" (FStar_Pervasives_Native.fst mangled_name))
end
| uu____2014 -> begin
()
end));
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[]))))));
)
end)))
in (

let rec extract_fv = (fun tm -> ((

let uu____2029 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2029) with
| true -> begin
(

let uu____2030 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "extract_fv term: %s\n" uu____2030))
end
| uu____2031 -> begin
()
end));
(

let uu____2032 = (

let uu____2033 = (FStar_Syntax_Subst.compress tm)
in uu____2033.FStar_Syntax_Syntax.n)
in (match (uu____2032) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____2041) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2048 = (

let uu____2057 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right uu____2057))
in (match (uu____2048) with
| (uu____2114, uu____2115, tysc, uu____2117) -> begin
(

let uu____2118 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____2118), (tysc)))
end)))
end
| uu____2119 -> begin
(failwith "Not an fv")
end));
))
in (

let extract_action = (fun g1 a -> ((

let uu____2145 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2145) with
| true -> begin
(

let uu____2146 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2147 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.print2 "Action type %s and term %s\n" uu____2146 uu____2147)))
end
| uu____2148 -> begin
()
end));
(

let uu____2149 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____2149) with
| (a_nm, a_lid) -> begin
(

let lbname = (

let uu____2165 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)) FStar_Syntax_Syntax.tun)
in FStar_Util.Inl (uu____2165))
in (

let lb = (FStar_Syntax_Syntax.mk_lb ((lbname), (a.FStar_Syntax_Syntax.action_univs), (FStar_Parser_Const.effect_Tot_lid), (a.FStar_Syntax_Syntax.action_typ), (a.FStar_Syntax_Syntax.action_defn)))
in (

let lbs = ((false), ((lb)::[]))
in (

let action_lb = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (

let uu____2191 = (FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb)
in (match (uu____2191) with
| (a_let, uu____2203, ty) -> begin
((

let uu____2206 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2206) with
| true -> begin
(

let uu____2207 = (FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let)
in (FStar_Util.print1 "Extracted action term: %s\n" uu____2207))
end
| uu____2208 -> begin
()
end));
(

let uu____2209 = (match (a_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____2218, uu____2219, (mllb)::[]), uu____2221) -> begin
(match (mllb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some (tysc) -> begin
((mllb.FStar_Extraction_ML_Syntax.mllb_def), (tysc))
end
| FStar_Pervasives_Native.None -> begin
(failwith "No type scheme")
end)
end
| uu____2241 -> begin
(failwith "Impossible")
end)
in (match (uu____2209) with
| (exp, tysc) -> begin
((

let uu____2253 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2253) with
| true -> begin
((

let uu____2255 = (FStar_Extraction_ML_Code.string_of_mlty a_nm (FStar_Pervasives_Native.snd tysc))
in (FStar_Util.print1 "Extracted action type: %s\n" uu____2255));
(FStar_List.iter (fun x -> (FStar_Util.print1 "and binders: %s\n" (FStar_Pervasives_Native.fst x))) (FStar_Pervasives_Native.fst tysc));
)
end
| uu____2266 -> begin
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

let uu____2267 = (

let uu____2272 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____2272) with
| (return_tm, ty_sc) -> begin
(

let uu____2285 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____2285) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____2267) with
| (g1, return_decl) -> begin
(

let uu____2304 = (

let uu____2309 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____2309) with
| (bind_tm, ty_sc) -> begin
(

let uu____2322 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____2322) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____2304) with
| (g2, bind_decl) -> begin
(

let uu____2341 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____2341) with
| (g3, actions) -> begin
((g3), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____2362) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2366, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____2374 = (

let uu____2375 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___153_2379 -> (match (uu___153_2379) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2380 -> begin
false
end))))
in (not (uu____2375)))
in (match (uu____2374) with
| true -> begin
((g), ([]))
end
| uu____2389 -> begin
(

let uu____2390 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2390) with
| (bs, uu____2410) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____2428 = (FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit FStar_Pervasives_Native.None)
in (extract_typ_abbrev g fv quals attrs uu____2428)))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____2430) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2446 = (

let uu____2455 = (FStar_TypeChecker_Env.open_universes_in g.FStar_Extraction_ML_UEnv.tcenv lb.FStar_Syntax_Syntax.lbunivs ((lb.FStar_Syntax_Syntax.lbdef)::(lb.FStar_Syntax_Syntax.lbtyp)::[]))
in (match (uu____2455) with
| (tcenv, uu____2479, def_typ) -> begin
(

let uu____2485 = (as_pair def_typ)
in ((tcenv), (uu____2485)))
end))
in (match (uu____2446) with
| (tcenv, (lbdef, lbtyp)) -> begin
(

let lbtyp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) tcenv lbtyp)
in (

let lbdef1 = (FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef lbtyp1)
in (

let uu____2509 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g uu____2509 quals se.FStar_Syntax_Syntax.sigattrs lbdef1))))
end)))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2511) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (

let tactic_registration_decl = (

let is_tactic_decl = (fun tac_lid h -> (match (h.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h', uu____2538) -> begin
(

let uu____2543 = (

let uu____2544 = (FStar_Syntax_Subst.compress h')
in uu____2544.FStar_Syntax_Syntax.n)
in (match (uu____2543) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.tactic_lid) -> begin
(

let uu____2548 = (

let uu____2549 = (FStar_Extraction_ML_Syntax.string_of_mlpath g.FStar_Extraction_ML_UEnv.currentModule)
in (FStar_Util.starts_with uu____2549 "FStar.Tactics"))
in (not (uu____2548)))
end
| uu____2550 -> begin
false
end))
end
| uu____2551 -> begin
false
end))
in (

let mk_registration = (fun tac_lid assm_lid t bs -> (

let h = (

let uu____2578 = (

let uu____2579 = (

let uu____2580 = (FStar_Ident.lid_of_str "FStar_Tactics_Native.register_tactic")
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2580))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____2579))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____2578))
in (

let lid_arg = (

let uu____2582 = (

let uu____2583 = (FStar_Ident.string_of_lid assm_lid)
in FStar_Extraction_ML_Syntax.MLC_String (uu____2583))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____2582))
in (

let tac_arity = (FStar_List.length bs)
in (

let arity = (

let uu____2590 = (

let uu____2591 = (

let uu____2592 = (FStar_Util.string_of_int (tac_arity + (Prims.parse_int "1")))
in (FStar_Ident.lid_of_str uu____2592))
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2591))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____2590))
in (

let tac_interpretation = (FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid lid_arg t bs)
in (

let app = (

let uu____2601 = (

let uu____2602 = (

let uu____2609 = (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) ((lid_arg)::(arity)::(tac_interpretation)::[]))
in ((h), (uu____2609)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2602))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____2601))
in FStar_Extraction_ML_Syntax.MLM_Top (app))))))))
in (match ((FStar_Pervasives_Native.snd lbs)) with
| (hd1)::[] -> begin
(

let uu____2619 = (FStar_Syntax_Util.arrow_formals_comp hd1.FStar_Syntax_Syntax.lbtyp)
in (match (uu____2619) with
| (bs, comp) -> begin
(

let t = (FStar_Syntax_Util.comp_result comp)
in (

let uu____2649 = (

let uu____2650 = (FStar_Syntax_Subst.compress t)
in uu____2650.FStar_Syntax_Syntax.n)
in (match (uu____2649) with
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let h1 = (FStar_Syntax_Subst.compress h)
in (

let tac_lid = (

let uu____2679 = (

let uu____2682 = (FStar_Util.right hd1.FStar_Syntax_Syntax.lbname)
in uu____2682.FStar_Syntax_Syntax.fv_name)
in uu____2679.FStar_Syntax_Syntax.v)
in (

let assm_lid = (

let uu____2684 = (FStar_All.pipe_left FStar_Ident.id_of_text (Prims.strcat "__" tac_lid.FStar_Ident.ident.FStar_Ident.idText))
in (FStar_Ident.lid_of_ns_and_id tac_lid.FStar_Ident.ns uu____2684))
in (

let uu____2685 = (is_tactic_decl assm_lid h1)
in (match (uu____2685) with
| true -> begin
(

let uu____2688 = (

let uu____2689 = (

let uu____2690 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____2690))
in (mk_registration tac_lid assm_lid uu____2689 bs))
in (uu____2688)::[])
end
| uu____2705 -> begin
[]
end)))))
end
| uu____2706 -> begin
[]
end)))
end))
end
| uu____2707 -> begin
[]
end)))
in (

let uu____2710 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (uu____2710) with
| (ml_let, uu____2724, uu____2725) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, uu____2733, bindings), uu____2735) -> begin
(

let uu____2748 = (FStar_List.fold_left2 (fun uu____2775 ml_lb uu____2777 -> (match (((uu____2775), (uu____2777))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____2799; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2801; FStar_Syntax_Syntax.lbdef = uu____2802}) -> begin
(

let lb_lid = (

let uu____2824 = (

let uu____2827 = (FStar_Util.right lbname)
in uu____2827.FStar_Syntax_Syntax.fv_name)
in uu____2824.FStar_Syntax_Syntax.v)
in (

let uu____2828 = (

let uu____2833 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___154_2838 -> (match (uu___154_2838) with
| FStar_Syntax_Syntax.Projector (uu____2839) -> begin
true
end
| uu____2844 -> begin
false
end))))
in (match (uu____2833) with
| true -> begin
(

let mname = (

let uu____2850 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____2850 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____2851 = (

let uu____2856 = (FStar_Util.right lbname)
in (

let uu____2857 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____2856 mname uu____2857 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____2851) with
| (env1, uu____2863) -> begin
((env1), ((

let uu___159_2865 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((FStar_Pervasives_Native.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = uu___159_2865.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___159_2865.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___159_2865.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = uu___159_2865.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____2868 -> begin
(

let uu____2869 = (

let uu____2870 = (

let uu____2875 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____2875 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2870))
in ((uu____2869), (ml_lb)))
end))
in (match (uu____2828) with
| (g1, ml_lb1) -> begin
((g1), ((ml_lb1)::ml_lbs))
end)))
end)) ((g), ([])) bindings (FStar_Pervasives_Native.snd lbs))
in (match (uu____2748) with
| (g1, ml_lbs') -> begin
(

let flags = (FStar_List.choose (fun uu___155_2910 -> (match (uu___155_2910) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____2913 -> begin
FStar_Pervasives_Native.None
end)) quals)
in (

let flags' = (FStar_List.choose (fun uu___156_2924 -> (match (uu___156_2924) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (data, uu____2930)); FStar_Syntax_Syntax.pos = uu____2931; FStar_Syntax_Syntax.vars = uu____2932} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Attribute ((FStar_Util.string_of_unicode data)))
end
| uu____2939 -> begin
((FStar_Util.print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message");
FStar_Pervasives_Native.None;
)
end)) attrs)
in (

let uu____2943 = (

let uu____2946 = (

let uu____2949 = (

let uu____2950 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____2950))
in (uu____2949)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.append flags flags')), ((FStar_List.rev ml_lbs')))))::[])
in (FStar_List.append uu____2946 tactic_registration_decl))
in ((g1), (uu____2943)))))
end))
end
| uu____2957 -> begin
(

let uu____2958 = (

let uu____2959 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____2959))
in (failwith uu____2958))
end)
end))))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2967, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2972 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____2972) with
| true -> begin
(

let always_fail = (

let imp = (

let uu____2983 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2983) with
| ([], t1) -> begin
(

let b = (

let uu____3012 = (FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3012))
in (

let uu____3013 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs ((b)::[]) uu____3013 FStar_Pervasives_Native.None)))
end
| (bs, t1) -> begin
(

let uu____3032 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____3032 FStar_Pervasives_Native.None))
end))
in (

let uu___160_3033 = se
in (

let uu____3034 = (

let uu____3035 = (

let uu____3042 = (

let uu____3049 = (

let uu____3052 = (

let uu____3053 = (

let uu____3058 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____3058))
in {FStar_Syntax_Syntax.lbname = uu____3053; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (uu____3052)::[])
in ((false), (uu____3049)))
in ((uu____3042), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____3035))
in {FStar_Syntax_Syntax.sigel = uu____3034; FStar_Syntax_Syntax.sigrng = uu___160_3033.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___160_3033.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___160_3033.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___160_3033.FStar_Syntax_Syntax.sigattrs})))
in (

let uu____3069 = (extract_sig g always_fail)
in (match (uu____3069) with
| (g1, mlm) -> begin
(

let uu____3088 = (FStar_Util.find_map quals (fun uu___157_3093 -> (match (uu___157_3093) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____3097 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____3088) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____3105 = (

let uu____3108 = (

let uu____3109 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____3109))
in (

let uu____3110 = (

let uu____3113 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____3113)::[])
in (uu____3108)::uu____3110))
in ((g1), (uu____3105)))
end
| uu____3116 -> begin
(

let uu____3119 = (FStar_Util.find_map quals (fun uu___158_3125 -> (match (uu___158_3125) with
| FStar_Syntax_Syntax.Projector (l, uu____3129) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____3130 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____3119) with
| FStar_Pervasives_Native.Some (uu____3137) -> begin
((g1), ([]))
end
| uu____3140 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____3145 -> begin
((g), ([]))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____3149 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____3149) with
| (ml_main, uu____3163, uu____3164) -> begin
(

let uu____3165 = (

let uu____3168 = (

let uu____3169 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____3169))
in (uu____3168)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____3165)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____3172) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_assume (uu____3179) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____3188) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____3191) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____3208 -> begin
()
end);
((g), ([]));
)
end);
))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (

let uu____3219 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____3219 FStar_Pervasives_Native.fst)))


let extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____3264 = (FStar_Options.debug_any ())
in (match (uu____3264) with
| true -> begin
(

let uu____3265 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" uu____3265))
end
| uu____3266 -> begin
()
end));
(

let uu____3267 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___161_3270 = g
in (

let uu____3271 = (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name)
in {FStar_Extraction_ML_UEnv.tcenv = uu____3271; FStar_Extraction_ML_UEnv.gamma = uu___161_3270.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___161_3270.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___161_3270.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = name}))
in (

let uu____3272 = (FStar_Util.fold_map extract_sig g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____3272) with
| (g2, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____3301 = (FStar_Options.codegen ())
in (match (uu____3301) with
| FStar_Pervasives_Native.Some ("Kremlin") -> begin
true
end
| uu____3304 -> begin
false
end))
in (

let uu____3307 = (((m.FStar_Syntax_Syntax.name.FStar_Ident.str <> "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface)))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (match (uu____3307) with
| true -> begin
((

let uu____3315 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____3315));
((g2), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (FStar_Pervasives_Native.Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____3374 -> begin
((g2), ([]))
end))))
end)))));
))




