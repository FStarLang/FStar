
open Prims
open FStar_Pervasives

let fail_exp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun lid t -> (

let uu____13 = (

let uu____20 = (

let uu____21 = (

let uu____36 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____37 = (

let uu____40 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____41 = (

let uu____44 = (

let uu____45 = (

let uu____46 = (

let uu____53 = (

let uu____54 = (

let uu____55 = (

let uu____60 = (

let uu____61 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" uu____61))
in ((uu____60), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (uu____55))
in FStar_Syntax_Syntax.Tm_constant (uu____54))
in (FStar_Syntax_Syntax.mk uu____53))
in (uu____46 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____45))
in (uu____44)::[])
in (uu____40)::uu____41))
in ((uu____36), (uu____37))))
in FStar_Syntax_Syntax.Tm_app (uu____21))
in (FStar_Syntax_Syntax.mk uu____20))
in (uu____13 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun id1 -> (FStar_Extraction_ML_Syntax.avoid_keyword id1.FStar_Ident.ident.FStar_Ident.idText))


let as_pair : 'Auu____84 . 'Auu____84 Prims.list  ->  ('Auu____84 * 'Auu____84) = (fun uu___70_95 -> (match (uu___70_95) with
| (a)::(b)::[] -> begin
((a), (b))
end
| uu____100 -> begin
(failwith "Expected a list with 2 elements")
end))


let rec extract_meta : FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option = (fun x -> (

let uu____114 = (FStar_Syntax_Subst.compress x)
in (match (uu____114) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____118; FStar_Syntax_Syntax.vars = uu____119} -> begin
(

let uu____122 = (

let uu____123 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____123))
in (match (uu____122) with
| "FStar.Pervasives.PpxDerivingShow" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.PpxDerivingShow)
end
| "FStar.Pervasives.CInline" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CInline)
end
| "FStar.Pervasives.Substitute" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Substitute)
end
| "FStar.Pervasives.Gc" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.GCType)
end
| uu____126 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____128; FStar_Syntax_Syntax.vars = uu____129}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____131)); FStar_Syntax_Syntax.pos = uu____132; FStar_Syntax_Syntax.vars = uu____133}, uu____134))::[]); FStar_Syntax_Syntax.pos = uu____135; FStar_Syntax_Syntax.vars = uu____136} -> begin
(

let uu____167 = (

let uu____168 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____168))
in (match (uu____167) with
| "FStar.Pervasives.PpxDerivingShowConstant" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant (s))
end
| "FStar.Pervasives.Comment" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Comment (s))
end
| "FStar.Pervasives.CPrologue" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CPrologue (s))
end
| "FStar.Pervasives.CEpilogue" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CEpilogue (s))
end
| "FStar.Pervasives.CConst" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CConst (s))
end
| uu____171 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("KremlinPrivate", uu____172)); FStar_Syntax_Syntax.pos = uu____173; FStar_Syntax_Syntax.vars = uu____174} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("c_inline", uu____177)); FStar_Syntax_Syntax.pos = uu____178; FStar_Syntax_Syntax.vars = uu____179} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CInline)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("substitute", uu____182)); FStar_Syntax_Syntax.pos = uu____183; FStar_Syntax_Syntax.vars = uu____184} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Substitute)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____188); FStar_Syntax_Syntax.pos = uu____189; FStar_Syntax_Syntax.vars = uu____190} -> begin
(extract_meta x1)
end
| uu____197 -> begin
FStar_Pervasives_Native.None
end)))


let extract_metadata : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Extraction_ML_Syntax.meta Prims.list = (fun metas -> (FStar_List.choose extract_meta metas))


let binders_as_mlty_binders : 'Auu____215 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____215) Prims.list  ->  (FStar_Extraction_ML_UEnv.env * Prims.string Prims.list) = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____255 -> (match (uu____255) with
| (bv, uu____265) -> begin
(

let uu____266 = (

let uu____267 = (

let uu____270 = (

let uu____271 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____271))
in FStar_Pervasives_Native.Some (uu____270))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____267))
in (

let uu____272 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____266), (uu____272))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals attrs def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def1 = (

let uu____314 = (

let uu____315 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right uu____315 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____314 FStar_Syntax_Util.un_uinst))
in (

let def2 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____317) -> begin
(FStar_Extraction_ML_Term.normalize_abs def1)
end
| uu____334 -> begin
def1
end)
in (

let uu____335 = (match (def2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____346) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____367 -> begin
(([]), (def2))
end)
in (match (uu____335) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___71_388 -> (match (uu___71_388) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____389 -> begin
false
end)) quals)
in (

let uu____390 = (binders_as_mlty_binders env bs)
in (match (uu____390) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____410 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____410 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____414 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___72_419 -> (match (uu___72_419) with
| FStar_Syntax_Syntax.Projector (uu____420) -> begin
true
end
| uu____425 -> begin
false
end))))
in (match (uu____414) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in FStar_Pervasives_Native.Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____429 -> begin
FStar_Pervasives_Native.None
end))
in (

let metadata = (extract_metadata attrs)
in (

let td = (

let uu____456 = (

let uu____477 = (lident_as_mlsymbol lid)
in ((assumed), (uu____477), (mangled_projector), (ml_bs), (metadata), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (uu____456)::[])
in (

let def3 = (

let uu____529 = (

let uu____530 = (

let uu____531 = (FStar_Ident.range_of_lid lid)
in (FStar_Extraction_ML_Util.mlloc_of_range uu____531))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____530))
in (uu____529)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env2 = (

let uu____533 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___73_537 -> (match (uu___73_537) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____538 -> begin
false
end))))
in (match (uu____533) with
| true -> begin
(FStar_Extraction_ML_UEnv.extend_type_name env1 fv)
end
| uu____539 -> begin
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
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list; imetadata : FStar_Extraction_ML_Syntax.metadata}


let __proj__Mkinductive_family__item__iname : inductive_family  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; imetadata = __fname__imetadata} -> begin
__fname__iname
end))


let __proj__Mkinductive_family__item__iparams : inductive_family  ->  FStar_Syntax_Syntax.binders = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; imetadata = __fname__imetadata} -> begin
__fname__iparams
end))


let __proj__Mkinductive_family__item__ityp : inductive_family  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; imetadata = __fname__imetadata} -> begin
__fname__ityp
end))


let __proj__Mkinductive_family__item__idatas : inductive_family  ->  data_constructor Prims.list = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; imetadata = __fname__imetadata} -> begin
__fname__idatas
end))


let __proj__Mkinductive_family__item__iquals : inductive_family  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; imetadata = __fname__imetadata} -> begin
__fname__iquals
end))


let __proj__Mkinductive_family__item__imetadata : inductive_family  ->  FStar_Extraction_ML_Syntax.metadata = (fun projectee -> (match (projectee) with
| {iname = __fname__iname; iparams = __fname__iparams; ityp = __fname__ityp; idatas = __fname__idatas; iquals = __fname__iquals; imetadata = __fname__imetadata} -> begin
__fname__imetadata
end))


let print_ifamily : inductive_family  ->  unit = (fun i -> (

let uu____703 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____704 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____705 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____706 = (

let uu____707 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____718 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____719 = (

let uu____720 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " uu____720))
in (Prims.strcat uu____718 uu____719))))))
in (FStar_All.pipe_right uu____707 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____703 uu____704 uu____705 uu____706))))))


let bundle_as_inductive_families : 'Auu____733 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____733  ->  FStar_Syntax_Syntax.attribute Prims.list  ->  (FStar_Extraction_ML_UEnv.env * inductive_family Prims.list) = (fun env ses quals attrs -> (

let uu____768 = (FStar_Util.fold_map (fun env1 se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas) -> begin
(

let uu____815 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____815) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____854, t2, l', nparams, uu____858) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____863 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____863) with
| (bs', body) -> begin
(

let uu____896 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____896) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____967 uu____968 -> (match (((uu____967), (uu____968))) with
| ((b', uu____986), (b, uu____988)) -> begin
(

let uu____997 = (

let uu____1004 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____1004)))
in FStar_Syntax_Syntax.NT (uu____997))
end)) bs_params bs1)
in (

let t3 = (

let uu____1006 = (

let uu____1009 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____1009))
in (FStar_All.pipe_right uu____1006 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____1014 -> begin
[]
end))))
in (

let metadata = (extract_metadata (FStar_List.append se.FStar_Syntax_Syntax.sigattrs attrs))
in (

let env2 = (

let uu____1019 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.extend_type_name env1 uu____1019))
in ((env2), (({iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = se.FStar_Syntax_Syntax.sigquals; imetadata = metadata})::[])))))
end))
end
| uu____1022 -> begin
((env1), ([]))
end)) env ses)
in (match (uu____768) with
| (env1, ifams) -> begin
((env1), ((FStar_List.flatten ifams)))
end)))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env1 ctor -> (

let mlt = (

let uu____1108 = (FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1108))
in (

let steps = (FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]
in (

let names1 = (

let uu____1115 = (

let uu____1116 = (

let uu____1119 = (FStar_TypeChecker_Normalize.normalize steps env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp)
in (FStar_Syntax_Subst.compress uu____1119))
in uu____1116.FStar_Syntax_Syntax.n)
in (match (uu____1115) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____1123) -> begin
(FStar_List.map (fun uu____1149 -> (match (uu____1149) with
| ({FStar_Syntax_Syntax.ppname = ppname; FStar_Syntax_Syntax.index = uu____1155; FStar_Syntax_Syntax.sort = uu____1156}, uu____1157) -> begin
ppname.FStar_Ident.idText
end)) bs)
end
| uu____1160 -> begin
[]
end))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____1171 = (

let uu____1172 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (FStar_Pervasives_Native.fst uu____1172))
in (

let uu____1177 = (

let uu____1188 = (lident_as_mlsymbol ctor.dname)
in (

let uu____1189 = (

let uu____1196 = (FStar_Extraction_ML_Util.argTypes mlt)
in (FStar_List.zip names1 uu____1196))
in ((uu____1188), (uu____1189))))
in ((uu____1171), (uu____1177))))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____1248 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____1248) with
| (env2, vars) -> begin
(

let uu____1283 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env2))
in (match (uu____1283) with
| (env3, ctors) -> begin
(

let uu____1376 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____1376) with
| (indices, uu____1412) -> begin
(

let ml_params = (

let uu____1432 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____1451 -> (

let uu____1456 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____1456)))))
in (FStar_List.append vars uu____1432))
in (

let tbody = (

let uu____1458 = (FStar_Util.find_opt (fun uu___74_1463 -> (match (uu___74_1463) with
| FStar_Syntax_Syntax.RecordType (uu____1464) -> begin
true
end
| uu____1473 -> begin
false
end)) ind.iquals)
in (match (uu____1458) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____1484 = (FStar_List.hd ctors)
in (match (uu____1484) with
| (uu____1505, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id1 uu____1542 -> (match (uu____1542) with
| (uu____1551, ty) -> begin
(

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id1)::[])))
in (

let uu____1554 = (lident_as_mlsymbol lid)
in ((uu____1554), (ty))))
end)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____1555 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____1558 = (

let uu____1577 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____1577), (FStar_Pervasives_Native.None), (ml_params), (ind.imetadata), (FStar_Pervasives_Native.Some (tbody))))
in ((env3), (uu____1558)))))
end))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____1611, t, uu____1613, uu____1614, uu____1615); FStar_Syntax_Syntax.sigrng = uu____1616; FStar_Syntax_Syntax.sigquals = uu____1617; FStar_Syntax_Syntax.sigmeta = uu____1618; FStar_Syntax_Syntax.sigattrs = uu____1619})::[], uu____1620), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____1637 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____1637) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____1683), quals) -> begin
(

let uu____1697 = (bundle_as_inductive_families env ses quals se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____1697) with
| (env1, ifams) -> begin
(

let uu____1718 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____1718) with
| (env2, td) -> begin
((env2), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end))
end))
end
| uu____1811 -> begin
(failwith "Unexpected signature element")
end))))


let maybe_register_plugin : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Extraction_ML_Syntax.mlmodule1 Prims.list = (fun g se -> (

let w = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
in (

let uu____1843 = ((

let uu____1846 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____1846 (FStar_Pervasives_Native.Some (FStar_Options.Plugin)))) || (

let uu____1852 = (FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs FStar_Parser_Const.plugin_attr)
in (not (uu____1852))))
in (match (uu____1843) with
| true -> begin
[]
end
| uu____1855 -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let mk_registration = (fun lb -> (

let fv = (

let uu____1875 = (

let uu____1878 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____1878.FStar_Syntax_Syntax.fv_name)
in uu____1875.FStar_Syntax_Syntax.v)
in (

let fv_t = lb.FStar_Syntax_Syntax.lbtyp
in (

let ml_name_str = (

let uu____1883 = (

let uu____1884 = (FStar_Ident.string_of_lid fv)
in FStar_Extraction_ML_Syntax.MLC_String (uu____1884))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____1883))
in (

let uu____1885 = (FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str)
in (match (uu____1885) with
| FStar_Pervasives_Native.Some (interp, arity, plugin) -> begin
(

let register = (match (plugin) with
| true -> begin
"FStar_Tactics_Native.register_plugin"
end
| uu____1906 -> begin
"FStar_Tactics_Native.register_tactic"
end)
in (

let h = (

let uu____1908 = (

let uu____1909 = (

let uu____1910 = (FStar_Ident.lid_of_str register)
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1910))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____1909))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1908))
in (

let arity1 = (

let uu____1912 = (

let uu____1913 = (

let uu____1924 = (FStar_Util.string_of_int arity)
in ((uu____1924), (FStar_Pervasives_Native.None)))
in FStar_Extraction_ML_Syntax.MLC_Int (uu____1913))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____1912))
in (

let app = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((h), (((w ml_name_str))::((w arity1))::(interp)::[])))))
in (FStar_Extraction_ML_Syntax.MLM_Top (app))::[]))))
end
| FStar_Pervasives_Native.None -> begin
[]
end))))))
in (FStar_List.collect mk_registration (FStar_Pervasives_Native.snd lbs)))
end
| uu____1946 -> begin
[]
end)
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____1973 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____1973))));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____1980) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1989) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____2006) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g1 lid ml_name tm tysc -> (

let uu____2054 = (

let uu____2059 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2059 ml_name tysc false false))
in (match (uu____2054) with
| (g2, mangled_name) -> begin
((

let uu____2067 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g2.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2067) with
| true -> begin
(FStar_Util.print1 "Mangled name: %s\n" mangled_name)
end
| uu____2068 -> begin
()
end));
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ((lb)::[]))))));
)
end)))
in (

let rec extract_fv = (fun tm -> ((

let uu____2083 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2083) with
| true -> begin
(

let uu____2084 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "extract_fv term: %s\n" uu____2084))
end
| uu____2085 -> begin
()
end));
(

let uu____2086 = (

let uu____2087 = (FStar_Syntax_Subst.compress tm)
in uu____2087.FStar_Syntax_Syntax.n)
in (match (uu____2086) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____2095) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2102 = (

let uu____2111 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right uu____2111))
in (match (uu____2102) with
| (uu____2168, uu____2169, tysc, uu____2171) -> begin
(

let uu____2172 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____2172), (tysc)))
end)))
end
| uu____2173 -> begin
(failwith "Not an fv")
end));
))
in (

let extract_action = (fun g1 a -> ((

let uu____2195 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2195) with
| true -> begin
(

let uu____2196 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2197 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.print2 "Action type %s and term %s\n" uu____2196 uu____2197)))
end
| uu____2198 -> begin
()
end));
(

let uu____2199 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____2199) with
| (a_nm, a_lid) -> begin
(

let lbname = (

let uu____2215 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)) FStar_Syntax_Syntax.tun)
in FStar_Util.Inl (uu____2215))
in (

let lb = (FStar_Syntax_Syntax.mk_lb ((lbname), (a.FStar_Syntax_Syntax.action_univs), (FStar_Parser_Const.effect_Tot_lid), (a.FStar_Syntax_Syntax.action_typ), (a.FStar_Syntax_Syntax.action_defn), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)))
in (

let lbs = ((false), ((lb)::[]))
in (

let action_lb = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (

let uu____2241 = (FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb)
in (match (uu____2241) with
| (a_let, uu____2253, ty) -> begin
((

let uu____2256 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2256) with
| true -> begin
(

let uu____2257 = (FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let)
in (FStar_Util.print1 "Extracted action term: %s\n" uu____2257))
end
| uu____2258 -> begin
()
end));
(

let uu____2259 = (match (a_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____2268, (mllb)::[]), uu____2270) -> begin
(match (mllb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some (tysc) -> begin
((mllb.FStar_Extraction_ML_Syntax.mllb_def), (tysc))
end
| FStar_Pervasives_Native.None -> begin
(failwith "No type scheme")
end)
end
| uu____2288 -> begin
(failwith "Impossible")
end)
in (match (uu____2259) with
| (exp, tysc) -> begin
((

let uu____2300 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2300) with
| true -> begin
((

let uu____2302 = (FStar_Extraction_ML_Code.string_of_mlty a_nm (FStar_Pervasives_Native.snd tysc))
in (FStar_Util.print1 "Extracted action type: %s\n" uu____2302));
(FStar_List.iter (fun x -> (FStar_Util.print1 "and binders: %s\n" x)) (FStar_Pervasives_Native.fst tysc));
)
end
| uu____2305 -> begin
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

let uu____2306 = (

let uu____2311 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____2311) with
| (return_tm, ty_sc) -> begin
(

let uu____2324 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____2324) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____2306) with
| (g1, return_decl) -> begin
(

let uu____2343 = (

let uu____2348 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____2348) with
| (bind_tm, ty_sc) -> begin
(

let uu____2361 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____2361) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____2343) with
| (g2, bind_decl) -> begin
(

let uu____2380 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____2380) with
| (g3, actions) -> begin
((g3), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_splice (uu____2401) -> begin
(failwith "impossible: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____2414) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2418, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____2426 = (

let uu____2427 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___75_2431 -> (match (uu___75_2431) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2432 -> begin
false
end))))
in (not (uu____2427)))
in (match (uu____2426) with
| true -> begin
((g), ([]))
end
| uu____2441 -> begin
(

let uu____2442 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2442) with
| (bs, uu____2462) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____2480 = (FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit FStar_Pervasives_Native.None)
in (extract_typ_abbrev g fv quals attrs uu____2480)))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____2482) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2498 = (

let uu____2507 = (FStar_TypeChecker_Env.open_universes_in g.FStar_Extraction_ML_UEnv.tcenv lb.FStar_Syntax_Syntax.lbunivs ((lb.FStar_Syntax_Syntax.lbdef)::(lb.FStar_Syntax_Syntax.lbtyp)::[]))
in (match (uu____2507) with
| (tcenv, uu____2531, def_typ) -> begin
(

let uu____2537 = (as_pair def_typ)
in ((tcenv), (uu____2537)))
end))
in (match (uu____2498) with
| (tcenv, (lbdef, lbtyp)) -> begin
(

let lbtyp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) tcenv lbtyp)
in (

let lbdef1 = (FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef lbtyp1)
in (

let uu____2561 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g uu____2561 quals se.FStar_Syntax_Syntax.sigattrs lbdef1))))
end)))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2563) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2574 = (

let uu____2581 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (FStar_Extraction_ML_Term.term_as_mlexpr g uu____2581))
in (match (uu____2574) with
| (ml_let, uu____2591, uu____2592) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, bindings), uu____2601) -> begin
(

let flags1 = (FStar_List.choose (fun uu___76_2616 -> (match (uu___76_2616) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____2619 -> begin
FStar_Pervasives_Native.None
end)) quals)
in (

let flags' = (extract_metadata attrs)
in (

let uu____2623 = (FStar_List.fold_left2 (fun uu____2649 ml_lb uu____2651 -> (match (((uu____2649), (uu____2651))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____2673; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2675; FStar_Syntax_Syntax.lbdef = uu____2676; FStar_Syntax_Syntax.lbattrs = uu____2677; FStar_Syntax_Syntax.lbpos = uu____2678}) -> begin
(

let uu____2703 = (FStar_All.pipe_right ml_lb.FStar_Extraction_ML_Syntax.mllb_meta (FStar_List.contains FStar_Extraction_ML_Syntax.Erased))
in (match (uu____2703) with
| true -> begin
((env), (ml_lbs))
end
| uu____2712 -> begin
(

let lb_lid = (

let uu____2714 = (

let uu____2717 = (FStar_Util.right lbname)
in uu____2717.FStar_Syntax_Syntax.fv_name)
in uu____2714.FStar_Syntax_Syntax.v)
in (

let flags'' = (

let uu____2721 = (

let uu____2722 = (FStar_Syntax_Subst.compress t)
in uu____2722.FStar_Syntax_Syntax.n)
in (match (uu____2721) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2727, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____2728; FStar_Syntax_Syntax.effect_name = e; FStar_Syntax_Syntax.result_typ = uu____2730; FStar_Syntax_Syntax.effect_args = uu____2731; FStar_Syntax_Syntax.flags = uu____2732}); FStar_Syntax_Syntax.pos = uu____2733; FStar_Syntax_Syntax.vars = uu____2734}) when (

let uu____2763 = (FStar_Ident.string_of_lid e)
in (Prims.op_Equality uu____2763 "FStar.HyperStack.ST.StackInline")) -> begin
(FStar_Extraction_ML_Syntax.StackInline)::[]
end
| uu____2764 -> begin
[]
end))
in (

let meta = (FStar_List.append flags1 (FStar_List.append flags' flags''))
in (

let ml_lb1 = (

let uu___80_2769 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = uu___80_2769.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = uu___80_2769.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___80_2769.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___80_2769.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu___80_2769.FStar_Extraction_ML_Syntax.print_typ})
in (

let uu____2770 = (

let uu____2775 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___77_2780 -> (match (uu___77_2780) with
| FStar_Syntax_Syntax.Projector (uu____2781) -> begin
true
end
| uu____2786 -> begin
false
end))))
in (match (uu____2775) with
| true -> begin
(

let mname = (

let uu____2792 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____2792 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____2793 = (

let uu____2798 = (FStar_Util.right lbname)
in (

let uu____2799 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____2798 mname uu____2799 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____2793) with
| (env1, uu____2805) -> begin
((env1), ((

let uu___81_2807 = ml_lb1
in {FStar_Extraction_ML_Syntax.mllb_name = (FStar_Pervasives_Native.snd mname); FStar_Extraction_ML_Syntax.mllb_tysc = uu___81_2807.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___81_2807.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___81_2807.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = uu___81_2807.FStar_Extraction_ML_Syntax.mllb_meta; FStar_Extraction_ML_Syntax.print_typ = uu___81_2807.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____2810 -> begin
(

let uu____2811 = (

let uu____2812 = (

let uu____2817 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____2817 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2812))
in ((uu____2811), (ml_lb1)))
end))
in (match (uu____2770) with
| (g1, ml_lb2) -> begin
((g1), ((ml_lb2)::ml_lbs))
end))))))
end))
end)) ((g), ([])) bindings (FStar_Pervasives_Native.snd lbs))
in (match (uu____2623) with
| (g1, ml_lbs') -> begin
(

let uu____2848 = (

let uu____2851 = (

let uu____2854 = (

let uu____2855 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____2855))
in (uu____2854)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.rev ml_lbs')))))::[])
in (

let uu____2858 = (maybe_register_plugin g1 se)
in (FStar_List.append uu____2851 uu____2858)))
in ((g1), (uu____2848)))
end))))
end
| uu____2863 -> begin
(

let uu____2864 = (

let uu____2865 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____2865))
in (failwith uu____2864))
end)
end))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2873, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2878 = ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) && (

let uu____2882 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.tcenv t)
in (not (uu____2882))))
in (match (uu____2878) with
| true -> begin
(

let always_fail = (

let imp = (

let uu____2891 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2891) with
| ([], t1) -> begin
(

let b = (

let uu____2920 = (FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2920))
in (

let uu____2921 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs ((b)::[]) uu____2921 FStar_Pervasives_Native.None)))
end
| (bs, t1) -> begin
(

let uu____2940 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____2940 FStar_Pervasives_Native.None))
end))
in (

let uu___82_2941 = se
in (

let uu____2942 = (

let uu____2943 = (

let uu____2950 = (

let uu____2957 = (

let uu____2960 = (

let uu____2961 = (

let uu____2966 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____2966))
in {FStar_Syntax_Syntax.lbname = uu____2961; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = imp.FStar_Syntax_Syntax.pos})
in (uu____2960)::[])
in ((false), (uu____2957)))
in ((uu____2950), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____2943))
in {FStar_Syntax_Syntax.sigel = uu____2942; FStar_Syntax_Syntax.sigrng = uu___82_2941.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___82_2941.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___82_2941.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___82_2941.FStar_Syntax_Syntax.sigattrs})))
in (

let uu____2979 = (extract_sig g always_fail)
in (match (uu____2979) with
| (g1, mlm) -> begin
(

let uu____2998 = (FStar_Util.find_map quals (fun uu___78_3003 -> (match (uu___78_3003) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____3007 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____2998) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____3015 = (

let uu____3018 = (

let uu____3019 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____3019))
in (

let uu____3020 = (

let uu____3023 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____3023)::[])
in (uu____3018)::uu____3020))
in ((g1), (uu____3015)))
end
| uu____3026 -> begin
(

let uu____3029 = (FStar_Util.find_map quals (fun uu___79_3035 -> (match (uu___79_3035) with
| FStar_Syntax_Syntax.Projector (l, uu____3039) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____3040 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____3029) with
| FStar_Pervasives_Native.Some (uu____3047) -> begin
((g1), ([]))
end
| uu____3050 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____3055 -> begin
((g), ([]))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____3059 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____3059) with
| (ml_main, uu____3073, uu____3074) -> begin
(

let uu____3075 = (

let uu____3078 = (

let uu____3079 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____3079))
in (uu____3078)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____3075)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____3082) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_assume (uu____3089) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____3098) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____3101) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng);
((g), ([]));
)
end);
))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (

let uu____3130 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____3130 FStar_Pervasives_Native.fst)))


let extract' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____3176 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___83_3179 = g
in (

let uu____3180 = (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name)
in {FStar_Extraction_ML_UEnv.tcenv = uu____3180; FStar_Extraction_ML_UEnv.gamma = uu___83_3179.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___83_3179.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___83_3179.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = name}))
in (

let uu____3181 = (FStar_Util.fold_map extract_sig g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____3181) with
| (g2, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____3210 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____3210 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin))))
in (

let uu____3215 = (((Prims.op_disEquality m.FStar_Syntax_Syntax.name.FStar_Ident.str "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface)))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (match (uu____3215) with
| true -> begin
((

let uu____3223 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____3223));
((g2), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (FStar_Pervasives_Native.Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____3282 -> begin
((g2), ([]))
end))))
end)))));
))


let extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let uu____3301 = (FStar_Options.debug_any ())
in (match (uu____3301) with
| true -> begin
(

let msg = (

let uu____3309 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.format1 "Extracting module %s\n" uu____3309))
in (FStar_Util.measure_execution_time msg (fun uu____3317 -> (extract' g m))))
end
| uu____3318 -> begin
(extract' g m)
end)))




