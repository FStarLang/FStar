
open Prims
open FStar_Pervasives

let fail_exp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun lid t -> (

let uu____9 = (

let uu____12 = (

let uu____13 = (

let uu____28 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____29 = (

let uu____32 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____33 = (

let uu____36 = (

let uu____37 = (

let uu____38 = (

let uu____41 = (

let uu____42 = (

let uu____43 = (

let uu____48 = (

let uu____49 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" uu____49))
in ((uu____48), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (uu____43))
in FStar_Syntax_Syntax.Tm_constant (uu____42))
in (FStar_Syntax_Syntax.mk uu____41))
in (uu____38 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____37))
in (uu____36)::[])
in (uu____32)::uu____33))
in ((uu____28), (uu____29))))
in FStar_Syntax_Syntax.Tm_app (uu____13))
in (FStar_Syntax_Syntax.mk uu____12))
in (uu____9 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun id1 -> (FStar_Extraction_ML_Syntax.avoid_keyword id1.FStar_Ident.ident.FStar_Ident.idText))


let as_pair : 'Auu____66 . 'Auu____66 Prims.list  ->  ('Auu____66 * 'Auu____66) = (fun uu___68_76 -> (match (uu___68_76) with
| (a)::(b)::[] -> begin
((a), (b))
end
| uu____81 -> begin
(failwith "Expected a list with 2 elements")
end))


let rec extract_meta : FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option = (fun x -> (

let uu____93 = (FStar_Syntax_Subst.compress x)
in (match (uu____93) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____97; FStar_Syntax_Syntax.vars = uu____98} -> begin
(

let uu____101 = (

let uu____102 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____102))
in (match (uu____101) with
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
| uu____105 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____107; FStar_Syntax_Syntax.vars = uu____108}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____110)); FStar_Syntax_Syntax.pos = uu____111; FStar_Syntax_Syntax.vars = uu____112}, uu____113))::[]); FStar_Syntax_Syntax.pos = uu____114; FStar_Syntax_Syntax.vars = uu____115} -> begin
(

let uu____146 = (

let uu____147 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____147))
in (match (uu____146) with
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
| uu____150 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("KremlinPrivate", uu____151)); FStar_Syntax_Syntax.pos = uu____152; FStar_Syntax_Syntax.vars = uu____153} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("c_inline", uu____156)); FStar_Syntax_Syntax.pos = uu____157; FStar_Syntax_Syntax.vars = uu____158} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CInline)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("substitute", uu____161)); FStar_Syntax_Syntax.pos = uu____162; FStar_Syntax_Syntax.vars = uu____163} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Substitute)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____167); FStar_Syntax_Syntax.pos = uu____168; FStar_Syntax_Syntax.vars = uu____169} -> begin
(extract_meta x1)
end
| uu____176 -> begin
FStar_Pervasives_Native.None
end)))


let extract_metadata : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Extraction_ML_Syntax.meta Prims.list = (fun metas -> (FStar_List.choose extract_meta metas))


let binders_as_mlty_binders : 'Auu____189 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____189) Prims.list  ->  (FStar_Extraction_ML_UEnv.env * Prims.string Prims.list) = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____227 -> (match (uu____227) with
| (bv, uu____237) -> begin
(

let uu____238 = (

let uu____239 = (

let uu____242 = (

let uu____243 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____243))
in FStar_Pervasives_Native.Some (uu____242))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____239))
in (

let uu____244 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____238), (uu____244))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals attrs def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def1 = (

let uu____276 = (

let uu____277 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right uu____277 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____276 FStar_Syntax_Util.un_uinst))
in (

let def2 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____279) -> begin
(FStar_Extraction_ML_Term.normalize_abs def1)
end
| uu____296 -> begin
def1
end)
in (

let uu____297 = (match (def2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____308) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____329 -> begin
(([]), (def2))
end)
in (match (uu____297) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___69_350 -> (match (uu___69_350) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____351 -> begin
false
end)) quals)
in (

let uu____352 = (binders_as_mlty_binders env bs)
in (match (uu____352) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____372 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____372 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____376 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___70_381 -> (match (uu___70_381) with
| FStar_Syntax_Syntax.Projector (uu____382) -> begin
true
end
| uu____387 -> begin
false
end))))
in (match (uu____376) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in FStar_Pervasives_Native.Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____391 -> begin
FStar_Pervasives_Native.None
end))
in (

let metadata = (extract_metadata attrs)
in (

let td = (

let uu____418 = (

let uu____439 = (lident_as_mlsymbol lid)
in ((assumed), (uu____439), (mangled_projector), (ml_bs), (metadata), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (uu____418)::[])
in (

let def3 = (

let uu____491 = (

let uu____492 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____492))
in (uu____491)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env2 = (

let uu____494 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___71_498 -> (match (uu___71_498) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____499 -> begin
false
end))))
in (match (uu____494) with
| true -> begin
(FStar_Extraction_ML_UEnv.extend_type_name env1 fv)
end
| uu____500 -> begin
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


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (

let uu____638 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____639 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____640 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____641 = (

let uu____642 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____653 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____654 = (

let uu____655 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " uu____655))
in (Prims.strcat uu____653 uu____654))))))
in (FStar_All.pipe_right uu____642 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____638 uu____639 uu____640 uu____641))))))


let bundle_as_inductive_families : 'Auu____663 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____663  ->  FStar_Syntax_Syntax.attribute Prims.list  ->  (FStar_Extraction_ML_UEnv.env * inductive_family Prims.list) = (fun env ses quals attrs -> (

let uu____694 = (FStar_Util.fold_map (fun env1 se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas) -> begin
(

let uu____741 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____741) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____780, t2, l', nparams, uu____784) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____789 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____789) with
| (bs', body) -> begin
(

let uu____822 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____822) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____893 uu____894 -> (match (((uu____893), (uu____894))) with
| ((b', uu____912), (b, uu____914)) -> begin
(

let uu____923 = (

let uu____930 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____930)))
in FStar_Syntax_Syntax.NT (uu____923))
end)) bs_params bs1)
in (

let t3 = (

let uu____932 = (

let uu____935 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____935))
in (FStar_All.pipe_right uu____932 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____940 -> begin
[]
end))))
in (

let metadata = (extract_metadata (FStar_List.append se.FStar_Syntax_Syntax.sigattrs attrs))
in (

let env2 = (

let uu____945 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.extend_type_name env1 uu____945))
in ((env2), (({iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = se.FStar_Syntax_Syntax.sigquals; imetadata = metadata})::[])))))
end))
end
| uu____948 -> begin
((env1), ([]))
end)) env ses)
in (match (uu____694) with
| (env1, ifams) -> begin
((env1), ((FStar_List.flatten ifams)))
end)))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env1 ctor -> (

let mlt = (

let uu____1024 = (FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1024))
in (

let steps = (FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]
in (

let names1 = (

let uu____1031 = (

let uu____1032 = (

let uu____1035 = (FStar_TypeChecker_Normalize.normalize steps env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp)
in (FStar_Syntax_Subst.compress uu____1035))
in uu____1032.FStar_Syntax_Syntax.n)
in (match (uu____1031) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____1039) -> begin
(FStar_List.map (fun uu____1065 -> (match (uu____1065) with
| ({FStar_Syntax_Syntax.ppname = ppname; FStar_Syntax_Syntax.index = uu____1071; FStar_Syntax_Syntax.sort = uu____1072}, uu____1073) -> begin
ppname.FStar_Ident.idText
end)) bs)
end
| uu____1076 -> begin
[]
end))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____1087 = (

let uu____1088 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (FStar_Pervasives_Native.fst uu____1088))
in (

let uu____1093 = (

let uu____1104 = (lident_as_mlsymbol ctor.dname)
in (

let uu____1105 = (

let uu____1112 = (FStar_Extraction_ML_Util.argTypes mlt)
in (FStar_List.zip names1 uu____1112))
in ((uu____1104), (uu____1105))))
in ((uu____1087), (uu____1093))))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____1160 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____1160) with
| (env2, vars) -> begin
(

let uu____1195 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env2))
in (match (uu____1195) with
| (env3, ctors) -> begin
(

let uu____1288 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____1288) with
| (indices, uu____1324) -> begin
(

let ml_params = (

let uu____1344 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____1363 -> (

let uu____1368 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____1368)))))
in (FStar_List.append vars uu____1344))
in (

let tbody = (

let uu____1370 = (FStar_Util.find_opt (fun uu___72_1375 -> (match (uu___72_1375) with
| FStar_Syntax_Syntax.RecordType (uu____1376) -> begin
true
end
| uu____1385 -> begin
false
end)) ind.iquals)
in (match (uu____1370) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____1396 = (FStar_List.hd ctors)
in (match (uu____1396) with
| (uu____1417, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id1 uu____1462 -> (match (uu____1462) with
| (uu____1471, ty) -> begin
(

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id1)::[])))
in (

let uu____1474 = (lident_as_mlsymbol lid)
in ((uu____1474), (ty))))
end)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____1475 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____1478 = (

let uu____1497 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____1497), (FStar_Pervasives_Native.None), (ml_params), (ind.imetadata), (FStar_Pervasives_Native.Some (tbody))))
in ((env3), (uu____1478)))))
end))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____1531, t, uu____1533, uu____1534, uu____1535); FStar_Syntax_Syntax.sigrng = uu____1536; FStar_Syntax_Syntax.sigquals = uu____1537; FStar_Syntax_Syntax.sigmeta = uu____1538; FStar_Syntax_Syntax.sigattrs = uu____1539})::[], uu____1540), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____1557 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____1557) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____1603), quals) -> begin
(

let uu____1617 = (bundle_as_inductive_families env ses quals se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____1617) with
| (env1, ifams) -> begin
(

let uu____1638 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____1638) with
| (env2, td) -> begin
((env2), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end))
end))
end
| uu____1731 -> begin
(failwith "Unexpected signature element")
end))))


let maybe_register_plugin : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Extraction_ML_Syntax.mlmodule1 Prims.list = (fun g se -> (

let w = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
in (

let uu____1757 = ((

let uu____1760 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____1760 (FStar_Pervasives_Native.Some (FStar_Options.Plugin)))) || (

let uu____1766 = (FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs FStar_Parser_Const.plugin_attr)
in (not (uu____1766))))
in (match (uu____1757) with
| true -> begin
[]
end
| uu____1769 -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let mk_registration = (fun lb -> (

let fv = (

let uu____1787 = (

let uu____1790 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____1790.FStar_Syntax_Syntax.fv_name)
in uu____1787.FStar_Syntax_Syntax.v)
in (

let fv_t = lb.FStar_Syntax_Syntax.lbtyp
in (

let ml_name_str = (

let uu____1795 = (

let uu____1796 = (FStar_Ident.string_of_lid fv)
in FStar_Extraction_ML_Syntax.MLC_String (uu____1796))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____1795))
in (

let uu____1797 = (FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str)
in (match (uu____1797) with
| FStar_Pervasives_Native.Some (interp, arity, plugin1) -> begin
(

let register = (match (plugin1) with
| true -> begin
"FStar_Tactics_Native.register_plugin"
end
| uu____1818 -> begin
"FStar_Tactics_Native.register_tactic"
end)
in (

let h = (

let uu____1820 = (

let uu____1821 = (

let uu____1822 = (FStar_Ident.lid_of_str register)
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1822))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____1821))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1820))
in (

let arity1 = (

let uu____1824 = (

let uu____1825 = (

let uu____1836 = (FStar_Util.string_of_int arity)
in ((uu____1836), (FStar_Pervasives_Native.None)))
in FStar_Extraction_ML_Syntax.MLC_Int (uu____1825))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____1824))
in (

let app = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((h), (((w ml_name_str))::((w arity1))::(interp)::[])))))
in (FStar_Extraction_ML_Syntax.MLM_Top (app))::[]))))
end
| FStar_Pervasives_Native.None -> begin
[]
end))))))
in (FStar_List.collect mk_registration (FStar_Pervasives_Native.snd lbs)))
end
| uu____1858 -> begin
[]
end)
end))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____1881 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____1881))));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____1888) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1897) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1914) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g1 lid ml_name tm tysc -> (

let uu____1952 = (

let uu____1957 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1957 ml_name tysc false false))
in (match (uu____1952) with
| (g2, mangled_name) -> begin
((

let uu____1965 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g2.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1965) with
| true -> begin
(FStar_Util.print1 "Mangled name: %s\n" mangled_name)
end
| uu____1966 -> begin
()
end));
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ((lb)::[]))))));
)
end)))
in (

let rec extract_fv = (fun tm -> ((

let uu____1979 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____1979) with
| true -> begin
(

let uu____1980 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "extract_fv term: %s\n" uu____1980))
end
| uu____1981 -> begin
()
end));
(

let uu____1982 = (

let uu____1983 = (FStar_Syntax_Subst.compress tm)
in uu____1983.FStar_Syntax_Syntax.n)
in (match (uu____1982) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____1991) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____1998 = (

let uu____2007 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right uu____2007))
in (match (uu____1998) with
| (uu____2064, uu____2065, tysc, uu____2067) -> begin
(

let uu____2068 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____2068), (tysc)))
end)))
end
| uu____2069 -> begin
(failwith "Not an fv")
end));
))
in (

let extract_action = (fun g1 a -> ((

let uu____2101 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2101) with
| true -> begin
(

let uu____2102 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2103 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.print2 "Action type %s and term %s\n" uu____2102 uu____2103)))
end
| uu____2104 -> begin
()
end));
(

let uu____2105 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____2105) with
| (a_nm, a_lid) -> begin
(

let lbname = (

let uu____2121 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)) FStar_Syntax_Syntax.tun)
in FStar_Util.Inl (uu____2121))
in (

let lb = (FStar_Syntax_Syntax.mk_lb ((lbname), (a.FStar_Syntax_Syntax.action_univs), (FStar_Parser_Const.effect_Tot_lid), (a.FStar_Syntax_Syntax.action_typ), (a.FStar_Syntax_Syntax.action_defn), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)))
in (

let lbs = ((false), ((lb)::[]))
in (

let action_lb = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (

let uu____2147 = (FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb)
in (match (uu____2147) with
| (a_let, uu____2159, ty) -> begin
((

let uu____2162 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2162) with
| true -> begin
(

let uu____2163 = (FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let)
in (FStar_Util.print1 "Extracted action term: %s\n" uu____2163))
end
| uu____2164 -> begin
()
end));
(

let uu____2165 = (match (a_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____2174, (mllb)::[]), uu____2176) -> begin
(match (mllb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some (tysc) -> begin
((mllb.FStar_Extraction_ML_Syntax.mllb_def), (tysc))
end
| FStar_Pervasives_Native.None -> begin
(failwith "No type scheme")
end)
end
| uu____2194 -> begin
(failwith "Impossible")
end)
in (match (uu____2165) with
| (exp, tysc) -> begin
((

let uu____2206 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2206) with
| true -> begin
((

let uu____2208 = (FStar_Extraction_ML_Code.string_of_mlty a_nm (FStar_Pervasives_Native.snd tysc))
in (FStar_Util.print1 "Extracted action type: %s\n" uu____2208));
(FStar_List.iter (fun x -> (FStar_Util.print1 "and binders: %s\n" x)) (FStar_Pervasives_Native.fst tysc));
)
end
| uu____2211 -> begin
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

let uu____2212 = (

let uu____2217 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____2217) with
| (return_tm, ty_sc) -> begin
(

let uu____2230 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____2230) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____2212) with
| (g1, return_decl) -> begin
(

let uu____2249 = (

let uu____2254 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____2254) with
| (bind_tm, ty_sc) -> begin
(

let uu____2267 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____2267) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____2249) with
| (g2, bind_decl) -> begin
(

let uu____2286 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____2286) with
| (g3, actions) -> begin
((g3), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_splice (uu____2307) -> begin
(failwith "impossible: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____2314) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2318, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____2326 = (

let uu____2327 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___73_2331 -> (match (uu___73_2331) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2332 -> begin
false
end))))
in (not (uu____2327)))
in (match (uu____2326) with
| true -> begin
((g), ([]))
end
| uu____2341 -> begin
(

let uu____2342 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2342) with
| (bs, uu____2362) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____2380 = (FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit FStar_Pervasives_Native.None)
in (extract_typ_abbrev g fv quals attrs uu____2380)))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____2382) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2398 = (

let uu____2407 = (FStar_TypeChecker_Env.open_universes_in g.FStar_Extraction_ML_UEnv.tcenv lb.FStar_Syntax_Syntax.lbunivs ((lb.FStar_Syntax_Syntax.lbdef)::(lb.FStar_Syntax_Syntax.lbtyp)::[]))
in (match (uu____2407) with
| (tcenv, uu____2431, def_typ) -> begin
(

let uu____2437 = (as_pair def_typ)
in ((tcenv), (uu____2437)))
end))
in (match (uu____2398) with
| (tcenv, (lbdef, lbtyp)) -> begin
(

let lbtyp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) tcenv lbtyp)
in (

let lbdef1 = (FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef lbtyp1)
in (

let uu____2461 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g uu____2461 quals se.FStar_Syntax_Syntax.sigattrs lbdef1))))
end)))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2463) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2474 = (

let uu____2481 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (FStar_Extraction_ML_Term.term_as_mlexpr g uu____2481))
in (match (uu____2474) with
| (ml_let, uu____2491, uu____2492) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, bindings), uu____2501) -> begin
(

let flags1 = (FStar_List.choose (fun uu___74_2516 -> (match (uu___74_2516) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____2519 -> begin
FStar_Pervasives_Native.None
end)) quals)
in (

let flags' = (extract_metadata attrs)
in (

let uu____2523 = (FStar_List.fold_left2 (fun uu____2555 ml_lb uu____2557 -> (match (((uu____2555), (uu____2557))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____2579; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2581; FStar_Syntax_Syntax.lbdef = uu____2582; FStar_Syntax_Syntax.lbattrs = uu____2583; FStar_Syntax_Syntax.lbpos = uu____2584}) -> begin
(

let lb_lid = (

let uu____2610 = (

let uu____2613 = (FStar_Util.right lbname)
in uu____2613.FStar_Syntax_Syntax.fv_name)
in uu____2610.FStar_Syntax_Syntax.v)
in (

let flags'' = (

let uu____2617 = (

let uu____2618 = (FStar_Syntax_Subst.compress t)
in uu____2618.FStar_Syntax_Syntax.n)
in (match (uu____2617) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2623, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____2624; FStar_Syntax_Syntax.effect_name = e; FStar_Syntax_Syntax.result_typ = uu____2626; FStar_Syntax_Syntax.effect_args = uu____2627; FStar_Syntax_Syntax.flags = uu____2628}); FStar_Syntax_Syntax.pos = uu____2629; FStar_Syntax_Syntax.vars = uu____2630}) when (

let uu____2659 = (FStar_Ident.string_of_lid e)
in (Prims.op_Equality uu____2659 "FStar.HyperStack.ST.StackInline")) -> begin
(FStar_Extraction_ML_Syntax.StackInline)::[]
end
| uu____2660 -> begin
[]
end))
in (

let meta = (FStar_List.append flags1 (FStar_List.append flags' flags''))
in (

let ml_lb1 = (

let uu___78_2665 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = uu___78_2665.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = uu___78_2665.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___78_2665.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___78_2665.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu___78_2665.FStar_Extraction_ML_Syntax.print_typ})
in (

let uu____2666 = (

let uu____2671 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___75_2676 -> (match (uu___75_2676) with
| FStar_Syntax_Syntax.Projector (uu____2677) -> begin
true
end
| uu____2682 -> begin
false
end))))
in (match (uu____2671) with
| true -> begin
(

let mname = (

let uu____2688 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____2688 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____2689 = (

let uu____2694 = (FStar_Util.right lbname)
in (

let uu____2695 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____2694 mname uu____2695 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____2689) with
| (env1, uu____2701) -> begin
((env1), ((

let uu___79_2703 = ml_lb1
in {FStar_Extraction_ML_Syntax.mllb_name = (FStar_Pervasives_Native.snd mname); FStar_Extraction_ML_Syntax.mllb_tysc = uu___79_2703.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___79_2703.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___79_2703.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = uu___79_2703.FStar_Extraction_ML_Syntax.mllb_meta; FStar_Extraction_ML_Syntax.print_typ = uu___79_2703.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____2706 -> begin
(

let uu____2707 = (

let uu____2708 = (

let uu____2713 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____2713 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2708))
in ((uu____2707), (ml_lb1)))
end))
in (match (uu____2666) with
| (g1, ml_lb2) -> begin
((g1), ((ml_lb2)::ml_lbs))
end))))))
end)) ((g), ([])) bindings (FStar_Pervasives_Native.snd lbs))
in (match (uu____2523) with
| (g1, ml_lbs') -> begin
(

let uu____2744 = (

let uu____2747 = (

let uu____2750 = (

let uu____2751 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____2751))
in (uu____2750)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.rev ml_lbs')))))::[])
in (

let uu____2754 = (maybe_register_plugin g1 se)
in (FStar_List.append uu____2747 uu____2754)))
in ((g1), (uu____2744)))
end))))
end
| uu____2759 -> begin
(

let uu____2760 = (

let uu____2761 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____2761))
in (failwith uu____2760))
end)
end))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2769, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2774 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____2774) with
| true -> begin
(

let always_fail = (

let imp = (

let uu____2785 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2785) with
| ([], t1) -> begin
(

let b = (

let uu____2814 = (FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2814))
in (

let uu____2815 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs ((b)::[]) uu____2815 FStar_Pervasives_Native.None)))
end
| (bs, t1) -> begin
(

let uu____2834 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____2834 FStar_Pervasives_Native.None))
end))
in (

let uu___80_2835 = se
in (

let uu____2836 = (

let uu____2837 = (

let uu____2844 = (

let uu____2851 = (

let uu____2854 = (

let uu____2855 = (

let uu____2860 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____2860))
in {FStar_Syntax_Syntax.lbname = uu____2855; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = imp.FStar_Syntax_Syntax.pos})
in (uu____2854)::[])
in ((false), (uu____2851)))
in ((uu____2844), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____2837))
in {FStar_Syntax_Syntax.sigel = uu____2836; FStar_Syntax_Syntax.sigrng = uu___80_2835.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___80_2835.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___80_2835.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___80_2835.FStar_Syntax_Syntax.sigattrs})))
in (

let uu____2873 = (extract_sig g always_fail)
in (match (uu____2873) with
| (g1, mlm) -> begin
(

let uu____2892 = (FStar_Util.find_map quals (fun uu___76_2897 -> (match (uu___76_2897) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____2901 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____2892) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____2909 = (

let uu____2912 = (

let uu____2913 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____2913))
in (

let uu____2914 = (

let uu____2917 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____2917)::[])
in (uu____2912)::uu____2914))
in ((g1), (uu____2909)))
end
| uu____2920 -> begin
(

let uu____2923 = (FStar_Util.find_map quals (fun uu___77_2929 -> (match (uu___77_2929) with
| FStar_Syntax_Syntax.Projector (l, uu____2933) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____2934 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____2923) with
| FStar_Pervasives_Native.Some (uu____2941) -> begin
((g1), ([]))
end
| uu____2944 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____2949 -> begin
((g), ([]))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2953 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____2953) with
| (ml_main, uu____2967, uu____2968) -> begin
(

let uu____2969 = (

let uu____2972 = (

let uu____2973 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____2973))
in (uu____2972)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____2969)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____2976) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_assume (uu____2983) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____2992) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2995) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng);
((g), ([]));
)
end);
))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (

let uu____3020 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____3020 FStar_Pervasives_Native.fst)))


let extract' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____3062 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___81_3065 = g
in (

let uu____3066 = (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name)
in {FStar_Extraction_ML_UEnv.tcenv = uu____3066; FStar_Extraction_ML_UEnv.gamma = uu___81_3065.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___81_3065.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___81_3065.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = name}))
in (

let uu____3067 = (FStar_Util.fold_map extract_sig g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____3067) with
| (g2, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____3096 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____3096 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin))))
in (

let uu____3101 = (((Prims.op_disEquality m.FStar_Syntax_Syntax.name.FStar_Ident.str "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface)))) && (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (match (uu____3101) with
| true -> begin
((

let uu____3109 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____3109));
((g2), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (FStar_Pervasives_Native.Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____3168 -> begin
((g2), ([]))
end))))
end)))));
))


let extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let uu____3183 = (FStar_Options.debug_any ())
in (match (uu____3183) with
| true -> begin
(

let msg = (

let uu____3191 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.format1 "Extracting module %s\n" uu____3191))
in (FStar_Util.measure_execution_time msg (fun uu____3199 -> (extract' g m))))
end
| uu____3200 -> begin
(extract' g m)
end)))




