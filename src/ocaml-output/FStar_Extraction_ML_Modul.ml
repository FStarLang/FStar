
open Prims
open FStar_Pervasives

type env_t =
FStar_Extraction_ML_UEnv.uenv


let fail_exp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun lid t -> (

let uu____25 = (

let uu____32 = (

let uu____33 = (

let uu____50 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____53 = (

let uu____64 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____73 = (

let uu____84 = (

let uu____93 = (

let uu____94 = (

let uu____101 = (

let uu____102 = (

let uu____103 = (

let uu____109 = (

let uu____111 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.op_Hat "Not yet implemented:" uu____111))
in ((uu____109), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (uu____103))
in FStar_Syntax_Syntax.Tm_constant (uu____102))
in (FStar_Syntax_Syntax.mk uu____101))
in (uu____94 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____93))
in (uu____84)::[])
in (uu____64)::uu____73))
in ((uu____50), (uu____53))))
in FStar_Syntax_Syntax.Tm_app (uu____33))
in (FStar_Syntax_Syntax.mk uu____32))
in (uu____25 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let always_fail : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lid t -> (

let imp = (

let uu____177 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____177) with
| ([], t1) -> begin
(

let b = (

let uu____220 = (FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____220))
in (

let uu____228 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs ((b)::[]) uu____228 FStar_Pervasives_Native.None)))
end
| (bs, t1) -> begin
(

let uu____265 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____265 FStar_Pervasives_Native.None))
end))
in (

let lb = (

let uu____269 = (

let uu____274 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____274))
in {FStar_Syntax_Syntax.lbname = uu____269; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = imp.FStar_Syntax_Syntax.pos})
in lb)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun id1 -> (FStar_Extraction_ML_Syntax.avoid_keyword id1.FStar_Ident.ident.FStar_Ident.idText))


let as_pair : 'Auu____296 . 'Auu____296 Prims.list  ->  ('Auu____296 * 'Auu____296) = (fun uu___0_307 -> (match (uu___0_307) with
| (a)::(b)::[] -> begin
((a), (b))
end
| uu____312 -> begin
(failwith "Expected a list with 2 elements")
end))


let flag_of_qual : FStar_Syntax_Syntax.qualifier  ->  FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option = (fun uu___1_327 -> (match (uu___1_327) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____330 -> begin
FStar_Pervasives_Native.None
end))


let rec extract_meta : FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option = (fun x -> (

let uu____339 = (FStar_Syntax_Subst.compress x)
in (match (uu____339) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____343; FStar_Syntax_Syntax.vars = uu____344} -> begin
(

let uu____347 = (

let uu____349 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____349))
in (match (uu____347) with
| "FStar.Pervasives.PpxDerivingShow" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.PpxDerivingShow)
end
| "FStar.Pervasives.PpxDerivingYoJson" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.PpxDerivingYoJson)
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
| "FStar.Pervasives.CAbstractStruct" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CAbstract)
end
| "FStar.Pervasives.CIfDef" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CIfDef)
end
| "FStar.Pervasives.CMacro" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CMacro)
end
| "Prims.deprecated" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Deprecated (""))
end
| uu____362 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____365; FStar_Syntax_Syntax.vars = uu____366}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____368)); FStar_Syntax_Syntax.pos = uu____369; FStar_Syntax_Syntax.vars = uu____370}, uu____371))::[]); FStar_Syntax_Syntax.pos = uu____372; FStar_Syntax_Syntax.vars = uu____373} -> begin
(

let uu____416 = (

let uu____418 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____418))
in (match (uu____416) with
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
| "FStar.Pervasives.CCConv" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CCConv (s))
end
| "Prims.deprecated" -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Deprecated (s))
end
| uu____428 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("KremlinPrivate", uu____430)); FStar_Syntax_Syntax.pos = uu____431; FStar_Syntax_Syntax.vars = uu____432} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("c_inline", uu____437)); FStar_Syntax_Syntax.pos = uu____438; FStar_Syntax_Syntax.vars = uu____439} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CInline)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("substitute", uu____444)); FStar_Syntax_Syntax.pos = uu____445; FStar_Syntax_Syntax.vars = uu____446} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Substitute)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____452); FStar_Syntax_Syntax.pos = uu____453; FStar_Syntax_Syntax.vars = uu____454} -> begin
(extract_meta x1)
end
| uu____461 -> begin
FStar_Pervasives_Native.None
end)))


let extract_metadata : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Extraction_ML_Syntax.meta Prims.list = (fun metas -> (FStar_List.choose extract_meta metas))


let binders_as_mlty_binders : 'Auu____481 . FStar_Extraction_ML_UEnv.uenv  ->  (FStar_Syntax_Syntax.bv * 'Auu____481) Prims.list  ->  (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list) = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____523 -> (match (uu____523) with
| (bv, uu____534) -> begin
(

let uu____535 = (

let uu____536 = (

let uu____539 = (

let uu____540 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____540))
in FStar_Pervasives_Native.Some (uu____539))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____536))
in (

let uu____542 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____535), (uu____542))))
end)) env bs))

type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}


let __proj__Mkdata_constructor__item__dname : data_constructor  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {dname = dname; dtyp = dtyp} -> begin
dname
end))


let __proj__Mkdata_constructor__item__dtyp : data_constructor  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {dname = dname; dtyp = dtyp} -> begin
dtyp
end))

type inductive_family =
{ifv : FStar_Syntax_Syntax.fv; iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list; imetadata : FStar_Extraction_ML_Syntax.metadata}


let __proj__Mkinductive_family__item__ifv : inductive_family  ->  FStar_Syntax_Syntax.fv = (fun projectee -> (match (projectee) with
| {ifv = ifv; iname = iname; iparams = iparams; ityp = ityp; idatas = idatas; iquals = iquals; imetadata = imetadata} -> begin
ifv
end))


let __proj__Mkinductive_family__item__iname : inductive_family  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {ifv = ifv; iname = iname; iparams = iparams; ityp = ityp; idatas = idatas; iquals = iquals; imetadata = imetadata} -> begin
iname
end))


let __proj__Mkinductive_family__item__iparams : inductive_family  ->  FStar_Syntax_Syntax.binders = (fun projectee -> (match (projectee) with
| {ifv = ifv; iname = iname; iparams = iparams; ityp = ityp; idatas = idatas; iquals = iquals; imetadata = imetadata} -> begin
iparams
end))


let __proj__Mkinductive_family__item__ityp : inductive_family  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {ifv = ifv; iname = iname; iparams = iparams; ityp = ityp; idatas = idatas; iquals = iquals; imetadata = imetadata} -> begin
ityp
end))


let __proj__Mkinductive_family__item__idatas : inductive_family  ->  data_constructor Prims.list = (fun projectee -> (match (projectee) with
| {ifv = ifv; iname = iname; iparams = iparams; ityp = ityp; idatas = idatas; iquals = iquals; imetadata = imetadata} -> begin
idatas
end))


let __proj__Mkinductive_family__item__iquals : inductive_family  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun projectee -> (match (projectee) with
| {ifv = ifv; iname = iname; iparams = iparams; ityp = ityp; idatas = idatas; iquals = iquals; imetadata = imetadata} -> begin
iquals
end))


let __proj__Mkinductive_family__item__imetadata : inductive_family  ->  FStar_Extraction_ML_Syntax.metadata = (fun projectee -> (match (projectee) with
| {ifv = ifv; iname = iname; iparams = iparams; ityp = ityp; idatas = idatas; iquals = iquals; imetadata = imetadata} -> begin
imetadata
end))


let print_ifamily : inductive_family  ->  unit = (fun i -> (

let uu____743 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____745 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____748 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____750 = (

let uu____752 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____766 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____768 = (

let uu____770 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.op_Hat " : " uu____770))
in (Prims.op_Hat uu____766 uu____768))))))
in (FStar_All.pipe_right uu____752 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____743 uu____745 uu____748 uu____750))))))


let bundle_as_inductive_families : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list) = (fun env ses quals -> (

let uu____815 = (FStar_Util.fold_map (fun env1 se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas) -> begin
(

let uu____863 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____863) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____902, t2, l', nparams, uu____906) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____913 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____913) with
| (bs', body) -> begin
(

let uu____952 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____952) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____1043 uu____1044 -> (match (((uu____1043), (uu____1044))) with
| ((b', uu____1070), (b, uu____1072)) -> begin
(

let uu____1093 = (

let uu____1100 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____1100)))
in FStar_Syntax_Syntax.NT (uu____1093))
end)) bs_params bs1)
in (

let t3 = (

let uu____1106 = (

let uu____1107 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____1107))
in (FStar_All.pipe_right uu____1106 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____1110 -> begin
[]
end))))
in (

let metadata = (

let uu____1114 = (extract_metadata se.FStar_Syntax_Syntax.sigattrs)
in (

let uu____1117 = (FStar_List.choose flag_of_qual quals)
in (FStar_List.append uu____1114 uu____1117)))
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let env2 = (FStar_Extraction_ML_UEnv.extend_type_name env1 fv)
in ((env2), (({ifv = fv; iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = se.FStar_Syntax_Syntax.sigquals; imetadata = metadata})::[]))))))
end))
end
| uu____1124 -> begin
((env1), ([]))
end)) env ses)
in (match (uu____815) with
| (env1, ifams) -> begin
((env1), ((FStar_List.flatten ifams)))
end)))

type iface =
{iface_module_name : FStar_Extraction_ML_Syntax.mlpath; iface_bindings : (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list; iface_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list; iface_type_names : FStar_Syntax_Syntax.fv Prims.list}


let __proj__Mkiface__item__iface_module_name : iface  ->  FStar_Extraction_ML_Syntax.mlpath = (fun projectee -> (match (projectee) with
| {iface_module_name = iface_module_name; iface_bindings = iface_bindings; iface_tydefs = iface_tydefs; iface_type_names = iface_type_names} -> begin
iface_module_name
end))


let __proj__Mkiface__item__iface_bindings : iface  ->  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list = (fun projectee -> (match (projectee) with
| {iface_module_name = iface_module_name; iface_bindings = iface_bindings; iface_tydefs = iface_tydefs; iface_type_names = iface_type_names} -> begin
iface_bindings
end))


let __proj__Mkiface__item__iface_tydefs : iface  ->  FStar_Extraction_ML_UEnv.tydef Prims.list = (fun projectee -> (match (projectee) with
| {iface_module_name = iface_module_name; iface_bindings = iface_bindings; iface_tydefs = iface_tydefs; iface_type_names = iface_type_names} -> begin
iface_tydefs
end))


let __proj__Mkiface__item__iface_type_names : iface  ->  FStar_Syntax_Syntax.fv Prims.list = (fun projectee -> (match (projectee) with
| {iface_module_name = iface_module_name; iface_bindings = iface_bindings; iface_tydefs = iface_tydefs; iface_type_names = iface_type_names} -> begin
iface_type_names
end))


let empty_iface : iface = {iface_module_name = (([]), ("")); iface_bindings = []; iface_tydefs = []; iface_type_names = []}


let iface_of_bindings : (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list  ->  iface = (fun fvs -> (

let uu___210_1304 = empty_iface
in {iface_module_name = uu___210_1304.iface_module_name; iface_bindings = fvs; iface_tydefs = uu___210_1304.iface_tydefs; iface_type_names = uu___210_1304.iface_type_names}))


let iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list  ->  iface = (fun tds -> (

let uu___213_1315 = empty_iface
in (

let uu____1316 = (FStar_List.map (fun td -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds)
in {iface_module_name = uu___213_1315.iface_module_name; iface_bindings = uu___213_1315.iface_bindings; iface_tydefs = tds; iface_type_names = uu____1316})))


let iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list  ->  iface = (fun fvs -> (

let uu___217_1331 = empty_iface
in {iface_module_name = uu___217_1331.iface_module_name; iface_bindings = uu___217_1331.iface_bindings; iface_tydefs = uu___217_1331.iface_tydefs; iface_type_names = fvs}))


let iface_union : iface  ->  iface  ->  iface = (fun if1 if2 -> (

let uu____1343 = (match ((Prims.op_disEquality if1.iface_module_name if1.iface_module_name)) with
| true -> begin
(failwith "Union not defined")
end
| uu____1346 -> begin
if1.iface_module_name
end)
in {iface_module_name = uu____1343; iface_bindings = (FStar_List.append if1.iface_bindings if2.iface_bindings); iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs); iface_type_names = (FStar_List.append if1.iface_type_names if2.iface_type_names)}))


let iface_union_l : iface Prims.list  ->  iface = (fun ifs -> (FStar_List.fold_right iface_union ifs empty_iface))


let mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.string = (fun p -> (FStar_String.concat ". " (FStar_List.append (FStar_Pervasives_Native.fst p) (((FStar_Pervasives_Native.snd p))::[]))))


let tscheme_to_string : 'Auu____1388 . FStar_Extraction_ML_Syntax.mlpath  ->  ('Auu____1388 * FStar_Extraction_ML_Syntax.mlty)  ->  Prims.string = (fun cm ts -> (FStar_Extraction_ML_Code.string_of_mlty cm (FStar_Pervasives_Native.snd ts)))


let print_exp_binding : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_UEnv.exp_binding  ->  Prims.string = (fun cm e -> (

let uu____1420 = (FStar_Extraction_ML_Code.string_of_mlexpr cm e.FStar_Extraction_ML_UEnv.exp_b_expr)
in (

let uu____1422 = (tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme)
in (

let uu____1424 = (FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok)
in (FStar_Util.format4 "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }" e.FStar_Extraction_ML_UEnv.exp_b_name uu____1420 uu____1422 uu____1424)))))


let print_binding : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)  ->  Prims.string = (fun cm uu____1442 -> (match (uu____1442) with
| (fv, exp_binding) -> begin
(

let uu____1450 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____1452 = (print_exp_binding cm exp_binding)
in (FStar_Util.format2 "(%s, %s)" uu____1450 uu____1452)))
end))


let print_tydef : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_UEnv.tydef  ->  Prims.string = (fun cm tydef -> (

let uu____1467 = (FStar_Syntax_Print.fv_to_string tydef.FStar_Extraction_ML_UEnv.tydef_fv)
in (

let uu____1469 = (tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def)
in (FStar_Util.format2 "(%s, %s)" uu____1467 uu____1469))))


let iface_to_string : iface  ->  Prims.string = (fun iface1 -> (

let cm = iface1.iface_module_name
in (

let print_type_name = (fun tn -> (FStar_Syntax_Print.fv_to_string tn))
in (

let uu____1487 = (

let uu____1489 = (FStar_List.map (print_binding cm) iface1.iface_bindings)
in (FStar_All.pipe_right uu____1489 (FStar_String.concat "\n")))
in (

let uu____1503 = (

let uu____1505 = (FStar_List.map (print_tydef cm) iface1.iface_tydefs)
in (FStar_All.pipe_right uu____1505 (FStar_String.concat "\n")))
in (

let uu____1515 = (

let uu____1517 = (FStar_List.map print_type_name iface1.iface_type_names)
in (FStar_All.pipe_right uu____1517 (FStar_String.concat "\n")))
in (FStar_Util.format4 "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}" (mlpath_to_string iface1.iface_module_name) uu____1487 uu____1503 uu____1515)))))))


let gamma_to_string : FStar_Extraction_ML_UEnv.uenv  ->  Prims.string = (fun env -> (

let cm = env.FStar_Extraction_ML_UEnv.currentModule
in (

let gamma = (FStar_List.collect (fun uu___2_1550 -> (match (uu___2_1550) with
| FStar_Extraction_ML_UEnv.Fv (b, e) -> begin
(((b), (e)))::[]
end
| uu____1567 -> begin
[]
end)) env.FStar_Extraction_ML_UEnv.env_bindings)
in (

let uu____1572 = (

let uu____1574 = (FStar_List.map (print_binding cm) gamma)
in (FStar_All.pipe_right uu____1574 (FStar_String.concat "\n")))
in (FStar_Util.format1 "Gamma = {\n %s }" uu____1572)))))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env quals attrs lb -> (

let uu____1634 = (

let uu____1643 = (FStar_TypeChecker_Env.open_universes_in env.FStar_Extraction_ML_UEnv.env_tcenv lb.FStar_Syntax_Syntax.lbunivs ((lb.FStar_Syntax_Syntax.lbdef)::(lb.FStar_Syntax_Syntax.lbtyp)::[]))
in (match (uu____1643) with
| (tcenv, uu____1661, def_typ) -> begin
(

let uu____1667 = (as_pair def_typ)
in ((tcenv), (uu____1667)))
end))
in (match (uu____1634) with
| (tcenv, (lbdef, lbtyp)) -> begin
(

let lbtyp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) tcenv lbtyp)
in (

let lbdef1 = (FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef lbtyp1)
in (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def = (

let uu____1698 = (

let uu____1699 = (FStar_Syntax_Subst.compress lbdef1)
in (FStar_All.pipe_right uu____1699 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____1698 FStar_Syntax_Util.un_uinst))
in (

let def1 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____1707) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| uu____1726 -> begin
def
end)
in (

let uu____1727 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1738) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____1763 -> begin
(([]), (def1))
end)
in (match (uu____1727) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___3_1783 -> (match (uu___3_1783) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1786 -> begin
false
end)) quals)
in (

let uu____1788 = (binders_as_mlty_binders env bs)
in (match (uu____1788) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____1815 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____1815 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____1820 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___4_1827 -> (match (uu___4_1827) with
| FStar_Syntax_Syntax.Projector (uu____1829) -> begin
true
end
| uu____1835 -> begin
false
end))))
in (match (uu____1820) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in FStar_Pervasives_Native.Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____1843 -> begin
FStar_Pervasives_Native.None
end))
in (

let metadata = (

let uu____1849 = (extract_metadata attrs)
in (

let uu____1852 = (FStar_List.choose flag_of_qual quals)
in (FStar_List.append uu____1849 uu____1852)))
in (

let td = (

let uu____1875 = (lident_as_mlsymbol lid)
in ((assumed), (uu____1875), (mangled_projector), (ml_bs), (metadata), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (

let def2 = (

let uu____1887 = (

let uu____1888 = (

let uu____1889 = (FStar_Ident.range_of_lid lid)
in (FStar_Extraction_ML_Util.mlloc_of_range uu____1889))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1888))
in (uu____1887)::(FStar_Extraction_ML_Syntax.MLM_Ty ((td)::[]))::[])
in (

let uu____1890 = (

let uu____1895 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___5_1901 -> (match (uu___5_1901) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____1905 -> begin
false
end))))
in (match (uu____1895) with
| true -> begin
(

let uu____1912 = (FStar_Extraction_ML_UEnv.extend_type_name env fv)
in ((uu____1912), ((iface_of_type_names ((fv)::[])))))
end
| uu____1913 -> begin
(

let uu____1915 = (FStar_Extraction_ML_UEnv.extend_tydef env fv td)
in (match (uu____1915) with
| (env2, tydef) -> begin
(

let uu____1926 = (iface_of_tydefs ((tydef)::[]))
in ((env2), (uu____1926)))
end))
end))
in (match (uu____1890) with
| (env2, iface1) -> begin
((env2), (iface1), (def2))
end)))))))
end)))
end))))))))
end)))


let extract_let_rec_type : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env quals attrs lb -> (

let lbtyp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env.FStar_Extraction_ML_UEnv.env_tcenv lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1985 = (FStar_Syntax_Util.arrow_formals lbtyp)
in (match (uu____1985) with
| (bs, uu____2009) -> begin
(

let uu____2030 = (binders_as_mlty_binders env bs)
in (match (uu____2030) with
| (env1, ml_bs) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let body = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let metadata = (

let uu____2062 = (extract_metadata attrs)
in (

let uu____2065 = (FStar_List.choose flag_of_qual quals)
in (FStar_List.append uu____2062 uu____2065)))
in (

let assumed = false
in (

let td = (

let uu____2091 = (lident_as_mlsymbol lid)
in ((assumed), (uu____2091), (FStar_Pervasives_Native.None), (ml_bs), (metadata), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body)))))
in (

let def = (

let uu____2104 = (

let uu____2105 = (

let uu____2106 = (FStar_Ident.range_of_lid lid)
in (FStar_Extraction_ML_Util.mlloc_of_range uu____2106))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____2105))
in (uu____2104)::(FStar_Extraction_ML_Syntax.MLM_Ty ((td)::[]))::[])
in (

let uu____2107 = (FStar_Extraction_ML_UEnv.extend_tydef env fv td)
in (match (uu____2107) with
| (env2, tydef) -> begin
(

let iface1 = (iface_of_tydefs ((tydef)::[]))
in ((env2), (iface1), (def)))
end)))))))))
end))
end))))


let extract_bundle_iface : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * iface) = (fun env se -> (

let extract_ctor = (fun env_iparams ml_tyvars env1 ctor -> (

let mlt = (

let uu____2188 = (FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2188))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____2195 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (match (uu____2195) with
| (env2, uu____2214, b) -> begin
((env2), (((fvv), (b))))
end))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____2253 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____2253) with
| (env_iparams, vars) -> begin
(

let uu____2281 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor env_iparams vars) env1))
in (match (uu____2281) with
| (env2, ctors) -> begin
((env2), (ctors))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____2345, t, uu____2347, uu____2348, uu____2349); FStar_Syntax_Syntax.sigrng = uu____2350; FStar_Syntax_Syntax.sigquals = uu____2351; FStar_Syntax_Syntax.sigmeta = uu____2352; FStar_Syntax_Syntax.sigattrs = uu____2353; FStar_Syntax_Syntax.sigopts = uu____2354})::[], uu____2355), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____2376 = (extract_ctor env [] env {dname = l; dtyp = t})
in (match (uu____2376) with
| (env1, ctor) -> begin
((env1), ((iface_of_bindings ((ctor)::[]))))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____2409), quals) -> begin
(

let uu____2423 = (FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs FStar_Parser_Const.erasable_attr)
in (match (uu____2423) with
| true -> begin
((env), (empty_iface))
end
| uu____2430 -> begin
(

let uu____2432 = (bundle_as_inductive_families env ses quals)
in (match (uu____2432) with
| (env1, ifams) -> begin
(

let uu____2449 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____2449) with
| (env2, td) -> begin
(

let uu____2490 = (

let uu____2491 = (

let uu____2492 = (FStar_List.map (fun x -> x.ifv) ifams)
in (iface_of_type_names uu____2492))
in (iface_union uu____2491 (iface_of_bindings (FStar_List.flatten td))))
in ((env2), (uu____2490)))
end))
end))
end))
end
| uu____2501 -> begin
(failwith "Unexpected signature element")
end))))


let extract_type_declaration : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g lid quals attrs univs1 t -> (

let uu____2576 = (

let uu____2578 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___6_2584 -> (match (uu___6_2584) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2587 -> begin
false
end))))
in (not (uu____2578)))
in (match (uu____2576) with
| true -> begin
((g), (empty_iface), ([]))
end
| uu____2600 -> begin
(

let uu____2602 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2602) with
| (bs, uu____2626) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let lb = (

let uu____2649 = (FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit FStar_Pervasives_Native.None)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____2649; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = t.FStar_Syntax_Syntax.pos})
in (extract_typ_abbrev g quals attrs lb)))
end))
end)))


let extract_reifiable_effect : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Extraction_ML_UEnv.uenv * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g ed -> (

let extend_env = (fun g1 lid ml_name tm tysc -> (

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (

let uu____2712 = (FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false)
in (match (uu____2712) with
| (g2, mangled_name, exp_binding) -> begin
((

let uu____2734 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g2.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2734) with
| true -> begin
(FStar_Util.print1 "Mangled name: %s\n" mangled_name)
end
| uu____2740 -> begin
()
end));
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), ((iface_of_bindings ((((fv), (exp_binding)))::[]))), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ((lb)::[]))))));
)
end))))
in (

let rec extract_fv = (fun tm -> ((

let uu____2770 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2770) with
| true -> begin
(

let uu____2775 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "extract_fv term: %s\n" uu____2775))
end
| uu____2778 -> begin
()
end));
(

let uu____2780 = (

let uu____2781 = (FStar_Syntax_Subst.compress tm)
in uu____2781.FStar_Syntax_Syntax.n)
in (match (uu____2780) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____2789) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2796 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (match (uu____2796) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____2801; FStar_Extraction_ML_UEnv.exp_b_expr = uu____2802; FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2804} -> begin
(

let uu____2807 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____2807), (tysc)))
end)))
end
| uu____2808 -> begin
(

let uu____2809 = (

let uu____2811 = (FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos)
in (

let uu____2813 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.format2 "(%s) Not an fv: %s" uu____2811 uu____2813)))
in (failwith uu____2809))
end));
))
in (

let extract_action = (fun g1 a -> ((

let uu____2841 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2841) with
| true -> begin
(

let uu____2846 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2848 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.print2 "Action type %s and term %s\n" uu____2846 uu____2848)))
end
| uu____2851 -> begin
()
end));
(

let uu____2853 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____2853) with
| (a_nm, a_lid) -> begin
(

let lbname = (

let uu____2873 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)) FStar_Syntax_Syntax.tun)
in FStar_Util.Inl (uu____2873))
in (

let lb = (FStar_Syntax_Syntax.mk_lb ((lbname), (a.FStar_Syntax_Syntax.action_univs), (FStar_Parser_Const.effect_Tot_lid), (a.FStar_Syntax_Syntax.action_typ), (a.FStar_Syntax_Syntax.action_defn), ([]), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)))
in (

let lbs = ((false), ((lb)::[]))
in (

let action_lb = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (

let uu____2903 = (FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb)
in (match (uu____2903) with
| (a_let, uu____2919, ty) -> begin
((

let uu____2922 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2922) with
| true -> begin
(

let uu____2927 = (FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let)
in (FStar_Util.print1 "Extracted action term: %s\n" uu____2927))
end
| uu____2930 -> begin
()
end));
(

let uu____2932 = (match (a_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____2955, (mllb)::[]), uu____2957) -> begin
(match (mllb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some (tysc) -> begin
((mllb.FStar_Extraction_ML_Syntax.mllb_def), (tysc))
end
| FStar_Pervasives_Native.None -> begin
(failwith "No type scheme")
end)
end
| uu____2997 -> begin
(failwith "Impossible")
end)
in (match (uu____2932) with
| (exp, tysc) -> begin
((

let uu____3035 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____3035) with
| true -> begin
((

let uu____3041 = (FStar_Extraction_ML_Code.string_of_mlty a_nm (FStar_Pervasives_Native.snd tysc))
in (FStar_Util.print1 "Extracted action type: %s\n" uu____3041));
(FStar_List.iter (fun x -> (FStar_Util.print1 "and binders: %s\n" x)) (FStar_Pervasives_Native.fst tysc));
)
end
| uu____3055 -> begin
()
end));
(

let uu____3057 = (extend_env g1 a_lid a_nm exp tysc)
in (match (uu____3057) with
| (env, iface1, impl) -> begin
((env), (((iface1), (impl))))
end));
)
end));
)
end))))))
end));
))
in (

let uu____3079 = (

let uu____3086 = (

let uu____3091 = (

let uu____3094 = (

let uu____3103 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr)
in (FStar_All.pipe_right uu____3103 FStar_Util.must))
in (FStar_All.pipe_right uu____3094 FStar_Pervasives_Native.snd))
in (extract_fv uu____3091))
in (match (uu____3086) with
| (return_tm, ty_sc) -> begin
(

let uu____3172 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____3172) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____3079) with
| (g1, return_iface, return_decl) -> begin
(

let uu____3197 = (

let uu____3204 = (

let uu____3209 = (

let uu____3212 = (

let uu____3221 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr)
in (FStar_All.pipe_right uu____3221 FStar_Util.must))
in (FStar_All.pipe_right uu____3212 FStar_Pervasives_Native.snd))
in (extract_fv uu____3209))
in (match (uu____3204) with
| (bind_tm, ty_sc) -> begin
(

let uu____3290 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____3290) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____3197) with
| (g2, bind_iface, bind_decl) -> begin
(

let uu____3315 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____3315) with
| (g3, actions) -> begin
(

let uu____3352 = (FStar_List.unzip actions)
in (match (uu____3352) with
| (actions_iface, actions1) -> begin
(

let uu____3379 = (iface_union_l ((return_iface)::(bind_iface)::actions_iface))
in ((g3), (uu____3379), ((return_decl)::(bind_decl)::actions1)))
end))
end))
end))
end))))))


let extract_let_rec_types : FStar_Syntax_Syntax.sigelt  ->  FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Extraction_ML_UEnv.uenv * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun se env lbs -> (

let uu____3410 = (FStar_Util.for_some (fun lb -> (

let uu____3415 = (FStar_Extraction_ML_Term.is_arity env lb.FStar_Syntax_Syntax.lbtyp)
in (not (uu____3415)))) lbs)
in (match (uu____3410) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ExtractionUnsupported), ("Mutually recursively defined typed and terms cannot yet be extracted")) se.FStar_Syntax_Syntax.sigrng)
end
| uu____3436 -> begin
(

let uu____3438 = (FStar_List.fold_left (fun uu____3473 lb -> (match (uu____3473) with
| (env1, iface_opt, impls) -> begin
(

let uu____3514 = (extract_let_rec_type env1 se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs lb)
in (match (uu____3514) with
| (env2, iface1, impl) -> begin
(

let iface_opt1 = (match (iface_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (iface1)
end
| FStar_Pervasives_Native.Some (iface') -> begin
(

let uu____3548 = (iface_union iface' iface1)
in FStar_Pervasives_Native.Some (uu____3548))
end)
in ((env2), (iface_opt1), ((impl)::impls)))
end))
end)) ((env), (FStar_Pervasives_Native.None), ([])) lbs)
in (match (uu____3438) with
| (env1, iface_opt, impls) -> begin
(

let uu____3588 = (FStar_Option.get iface_opt)
in (

let uu____3589 = (FStar_All.pipe_right (FStar_List.rev impls) FStar_List.flatten)
in ((env1), (uu____3588), (uu____3589))))
end))
end)))


let extract_sigelt_iface : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.uenv * iface) = (fun g se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____3621) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3630) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____3647) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____3666 = (extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs univs1 t)
in (match (uu____3666) with
| (env, iface1, uu____3681) -> begin
((env), (iface1))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____3687) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____3696 = (extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs lb)
in (match (uu____3696) with
| (env, iface1, uu____3711) -> begin
((env), (iface1))
end))
end
| FStar_Syntax_Syntax.Sig_let ((true, lbs), uu____3717) when (FStar_Util.for_some (fun lb -> (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp)) lbs) -> begin
(

let uu____3730 = (extract_let_rec_types se g lbs)
in (match (uu____3730) with
| (env, iface1, uu____3745) -> begin
((env), (iface1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _univs, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____3756 = ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) && (

let uu____3762 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (not (uu____3762))))
in (match (uu____3756) with
| true -> begin
(

let uu____3769 = (

let uu____3780 = (

let uu____3781 = (

let uu____3784 = (always_fail lid t)
in (uu____3784)::[])
in ((false), (uu____3781)))
in (FStar_Extraction_ML_Term.extract_lb_iface g uu____3780))
in (match (uu____3769) with
| (g1, bindings) -> begin
((g1), ((iface_of_bindings bindings)))
end))
end
| uu____3807 -> begin
((g), (empty_iface))
end)))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____3810) -> begin
(

let uu____3815 = (FStar_Extraction_ML_Term.extract_lb_iface g lbs)
in (match (uu____3815) with
| (g1, bindings) -> begin
((g1), ((iface_of_bindings bindings)))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____3844) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_assume (uu____3845) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____3852) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____3853) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng);
((g), (empty_iface));
)
end
| FStar_Syntax_Syntax.Sig_splice (uu____3868) -> begin
(failwith "impossible: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____3881 = ((FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname) && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders))
in (match (uu____3881) with
| true -> begin
(

let uu____3894 = (extract_reifiable_effect g ed)
in (match (uu____3894) with
| (env, iface1, uu____3909) -> begin
((env), (iface1))
end))
end
| uu____3914 -> begin
((g), (empty_iface))
end))
end))


let extract_iface' : env_t  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.uenv * iface) = (fun g modul -> (

let uu____3931 = (FStar_Options.interactive ())
in (match (uu____3931) with
| true -> begin
((g), (empty_iface))
end
| uu____3938 -> begin
(

let uu____3940 = (FStar_Options.restore_cmd_line_options true)
in (

let decls = modul.FStar_Syntax_Syntax.declarations
in (

let iface1 = (

let uu___611_3944 = empty_iface
in {iface_module_name = g.FStar_Extraction_ML_UEnv.currentModule; iface_bindings = uu___611_3944.iface_bindings; iface_tydefs = uu___611_3944.iface_tydefs; iface_type_names = uu___611_3944.iface_type_names})
in (

let res = (FStar_List.fold_left (fun uu____3962 se -> (match (uu____3962) with
| (g1, iface2) -> begin
(

let uu____3974 = (extract_sigelt_iface g1 se)
in (match (uu____3974) with
| (g2, iface') -> begin
(

let uu____3985 = (iface_union iface2 iface')
in ((g2), (uu____3985)))
end))
end)) ((g), (iface1)) decls)
in ((

let uu____3987 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_left (fun a1 -> ()) uu____3987));
res;
)))))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.uenv * iface) = (fun g modul -> (

let uu____4004 = (FStar_Options.debug_any ())
in (match (uu____4004) with
| true -> begin
(

let uu____4011 = (FStar_Util.format1 "Extracted interface of %s" modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (FStar_Util.measure_execution_time uu____4011 (fun uu____4019 -> (extract_iface' g modul))))
end
| uu____4020 -> begin
(extract_iface' g modul)
end)))


let extend_with_iface : FStar_Extraction_ML_UEnv.uenv  ->  iface  ->  FStar_Extraction_ML_UEnv.uenv = (fun g iface1 -> (

let mlident_map = (FStar_List.fold_left (fun acc uu____4049 -> (match (uu____4049) with
| (uu____4060, x) -> begin
(FStar_Util.psmap_add acc x.FStar_Extraction_ML_UEnv.exp_b_name "")
end)) g.FStar_Extraction_ML_UEnv.env_mlident_map iface1.iface_bindings)
in (

let uu___634_4064 = g
in (

let uu____4065 = (

let uu____4068 = (FStar_List.map (fun _4075 -> FStar_Extraction_ML_UEnv.Fv (_4075)) iface1.iface_bindings)
in (FStar_List.append uu____4068 g.FStar_Extraction_ML_UEnv.env_bindings))
in {FStar_Extraction_ML_UEnv.env_tcenv = uu___634_4064.FStar_Extraction_ML_UEnv.env_tcenv; FStar_Extraction_ML_UEnv.env_bindings = uu____4065; FStar_Extraction_ML_UEnv.env_mlident_map = mlident_map; FStar_Extraction_ML_UEnv.tydefs = (FStar_List.append iface1.iface_tydefs g.FStar_Extraction_ML_UEnv.tydefs); FStar_Extraction_ML_UEnv.type_names = (FStar_List.append iface1.iface_type_names g.FStar_Extraction_ML_UEnv.type_names); FStar_Extraction_ML_UEnv.currentModule = uu___634_4064.FStar_Extraction_ML_UEnv.currentModule}))))


let extract_bundle : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun env_iparams ml_tyvars env1 ctor -> (

let mlt = (

let uu____4153 = (FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4153))
in (

let steps = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]
in (

let names1 = (

let uu____4161 = (

let uu____4162 = (

let uu____4165 = (FStar_TypeChecker_Normalize.normalize steps env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp)
in (FStar_Syntax_Subst.compress uu____4165))
in uu____4162.FStar_Syntax_Syntax.n)
in (match (uu____4161) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____4170) -> begin
(FStar_List.map (fun uu____4203 -> (match (uu____4203) with
| ({FStar_Syntax_Syntax.ppname = ppname; FStar_Syntax_Syntax.index = uu____4212; FStar_Syntax_Syntax.sort = uu____4213}, uu____4214) -> begin
ppname.FStar_Ident.idText
end)) bs)
end
| uu____4222 -> begin
[]
end))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____4230 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (match (uu____4230) with
| (env2, uu____4257, uu____4258) -> begin
(

let uu____4261 = (

let uu____4274 = (lident_as_mlsymbol ctor.dname)
in (

let uu____4276 = (

let uu____4284 = (FStar_Extraction_ML_Util.argTypes mlt)
in (FStar_List.zip names1 uu____4284))
in ((uu____4274), (uu____4276))))
in ((env2), (uu____4261)))
end))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____4345 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____4345) with
| (env_iparams, vars) -> begin
(

let uu____4389 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor env_iparams vars) env1))
in (match (uu____4389) with
| (env2, ctors) -> begin
(

let uu____4496 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____4496) with
| (indices, uu____4538) -> begin
(

let ml_params = (

let uu____4563 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____4589 -> (

let uu____4597 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "\'dummyV" uu____4597)))))
in (FStar_List.append vars uu____4563))
in (

let tbody = (

let uu____4602 = (FStar_Util.find_opt (fun uu___7_4607 -> (match (uu___7_4607) with
| FStar_Syntax_Syntax.RecordType (uu____4609) -> begin
true
end
| uu____4619 -> begin
false
end)) ind.iquals)
in (match (uu____4602) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____4631 = (FStar_List.hd ctors)
in (match (uu____4631) with
| (uu____4656, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id1 uu____4700 -> (match (uu____4700) with
| (uu____4711, ty) -> begin
(

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id1)::[])))
in (

let uu____4716 = (lident_as_mlsymbol lid)
in ((uu____4716), (ty))))
end)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____4719 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____4722 = (

let uu____4745 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____4745), (FStar_Pervasives_Native.None), (ml_params), (ind.imetadata), (FStar_Pervasives_Native.Some (tbody))))
in ((env2), (uu____4722)))))
end))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____4790, t, uu____4792, uu____4793, uu____4794); FStar_Syntax_Syntax.sigrng = uu____4795; FStar_Syntax_Syntax.sigquals = uu____4796; FStar_Syntax_Syntax.sigmeta = uu____4797; FStar_Syntax_Syntax.sigattrs = uu____4798; FStar_Syntax_Syntax.sigopts = uu____4799})::[], uu____4800), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____4821 = (extract_ctor env [] env {dname = l; dtyp = t})
in (match (uu____4821) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____4874), quals) -> begin
(

let uu____4888 = (FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs FStar_Parser_Const.erasable_attr)
in (match (uu____4888) with
| true -> begin
((env), ([]))
end
| uu____4899 -> begin
(

let uu____4901 = (bundle_as_inductive_families env ses quals)
in (match (uu____4901) with
| (env1, ifams) -> begin
(

let uu____4920 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____4920) with
| (env2, td) -> begin
((env2), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end))
end))
end))
end
| uu____5029 -> begin
(failwith "Unexpected signature element")
end))))


let maybe_register_plugin : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Extraction_ML_Syntax.mlmodule1 Prims.list = (fun g se -> (

let w = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
in (

let plugin_with_arity = (fun attrs -> (FStar_Util.find_map attrs (fun t -> (

let uu____5087 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____5087) with
| (head1, args) -> begin
(

let uu____5135 = (

let uu____5137 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr head1)
in (not (uu____5137)))
in (match (uu____5135) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5148 -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, uu____5156)); FStar_Syntax_Syntax.pos = uu____5157; FStar_Syntax_Syntax.vars = uu____5158}, uu____5159))::[] -> begin
(

let uu____5198 = (

let uu____5202 = (FStar_Util.int_of_string s)
in FStar_Pervasives_Native.Some (uu____5202))
in FStar_Pervasives_Native.Some (uu____5198))
end
| uu____5208 -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end)
end))
end)))))
in (

let uu____5223 = (

let uu____5225 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____5225 (FStar_Pervasives_Native.Some (FStar_Options.Plugin))))
in (match (uu____5223) with
| true -> begin
[]
end
| uu____5233 -> begin
(

let uu____5235 = (plugin_with_arity se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____5235) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (arity_opt) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let mk_registration = (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let fv_lid1 = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let fv_t = lb.FStar_Syntax_Syntax.lbtyp
in (

let ml_name_str = (

let uu____5277 = (

let uu____5278 = (FStar_Ident.string_of_lid fv_lid1)
in FStar_Extraction_ML_Syntax.MLC_String (uu____5278))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____5277))
in (

let uu____5280 = (FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t arity_opt ml_name_str)
in (match (uu____5280) with
| FStar_Pervasives_Native.Some (interp, nbe_interp, arity, plugin1) -> begin
(

let uu____5313 = (match (plugin1) with
| true -> begin
(("FStar_Tactics_Native.register_plugin"), ((interp)::(nbe_interp)::[]))
end
| uu____5333 -> begin
(("FStar_Tactics_Native.register_tactic"), ((interp)::[]))
end)
in (match (uu____5313) with
| (register, args) -> begin
(

let h = (

let uu____5350 = (

let uu____5351 = (

let uu____5352 = (FStar_Ident.lid_of_str register)
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5352))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____5351))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____5350))
in (

let arity1 = (

let uu____5354 = (

let uu____5355 = (

let uu____5367 = (FStar_Util.string_of_int arity)
in ((uu____5367), (FStar_Pervasives_Native.None)))
in FStar_Extraction_ML_Syntax.MLC_Int (uu____5355))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____5354))
in (

let app = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((h), ((FStar_List.append (((w ml_name_str))::((w arity1))::[]) args))))))
in (FStar_Extraction_ML_Syntax.MLM_Top (app))::[])))
end))
end
| FStar_Pervasives_Native.None -> begin
[]
end)))))))
in (FStar_List.collect mk_registration (FStar_Pervasives_Native.snd lbs)))
end
| uu____5396 -> begin
[]
end)
end))
end)))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5424 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____5424))));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____5433) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5442) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____5459) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) when (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname) -> begin
(

let uu____5476 = (extract_reifiable_effect g ed)
in (match (uu____5476) with
| (env, _iface, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_splice (uu____5500) -> begin
(failwith "impossible: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____5514) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____5520 = (extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs univs1 t)
in (match (uu____5520) with
| (env, uu____5536, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____5545) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____5554 = (extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs lb)
in (match (uu____5554) with
| (env, uu____5570, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_let ((true, lbs), uu____5579) when (FStar_Util.for_some (fun lb -> (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp)) lbs) -> begin
(

let uu____5592 = (extract_let_rec_types se g lbs)
in (match (uu____5592) with
| (env, uu____5608, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____5617) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____5628 = (

let uu____5637 = (FStar_Syntax_Util.extract_attr' FStar_Parser_Const.postprocess_extr_with attrs)
in (match (uu____5637) with
| FStar_Pervasives_Native.None -> begin
((attrs), (FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.Some (ats, ((tau, FStar_Pervasives_Native.None))::uu____5666) -> begin
((ats), (FStar_Pervasives_Native.Some (tau)))
end
| FStar_Pervasives_Native.Some (ats, args) -> begin
((FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng ((FStar_Errors.Warning_UnrecognizedAttribute), ("Ill-formed application of `postprocess_for_extraction_with`")));
((attrs), (FStar_Pervasives_Native.None));
)
end))
in (match (uu____5628) with
| (attrs1, post_tau) -> begin
(

let postprocess_lb = (fun tau lb -> (

let lbdef = (FStar_TypeChecker_Env.postprocess g.FStar_Extraction_ML_UEnv.env_tcenv tau lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___866_5752 = lb
in {FStar_Syntax_Syntax.lbname = uu___866_5752.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___866_5752.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___866_5752.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___866_5752.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___866_5752.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___866_5752.FStar_Syntax_Syntax.lbpos})))
in (

let lbs1 = (

let uu____5761 = (match (post_tau) with
| FStar_Pervasives_Native.Some (tau) -> begin
(FStar_List.map (postprocess_lb tau) (FStar_Pervasives_Native.snd lbs))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives_Native.snd lbs)
end)
in (((FStar_Pervasives_Native.fst lbs)), (uu____5761)))
in (

let uu____5779 = (

let uu____5786 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs1), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (FStar_Extraction_ML_Term.term_as_mlexpr g uu____5786))
in (match (uu____5779) with
| (ml_let, uu____5803, uu____5804) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, bindings), uu____5813) -> begin
(

let flags = (FStar_List.choose flag_of_qual quals)
in (

let flags' = (extract_metadata attrs1)
in (

let uu____5830 = (FStar_List.fold_left2 (fun uu____5856 ml_lb uu____5858 -> (match (((uu____5856), (uu____5858))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____5880; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____5882; FStar_Syntax_Syntax.lbdef = uu____5883; FStar_Syntax_Syntax.lbattrs = uu____5884; FStar_Syntax_Syntax.lbpos = uu____5885}) -> begin
(

let uu____5910 = (FStar_All.pipe_right ml_lb.FStar_Extraction_ML_Syntax.mllb_meta (FStar_List.contains FStar_Extraction_ML_Syntax.Erased))
in (match (uu____5910) with
| true -> begin
((env), (ml_lbs))
end
| uu____5924 -> begin
(

let lb_lid = (

let uu____5927 = (

let uu____5930 = (FStar_Util.right lbname)
in uu____5930.FStar_Syntax_Syntax.fv_name)
in uu____5927.FStar_Syntax_Syntax.v)
in (

let flags'' = (

let uu____5934 = (

let uu____5935 = (FStar_Syntax_Subst.compress t)
in uu____5935.FStar_Syntax_Syntax.n)
in (match (uu____5934) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5940, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5941; FStar_Syntax_Syntax.effect_name = e; FStar_Syntax_Syntax.result_typ = uu____5943; FStar_Syntax_Syntax.effect_args = uu____5944; FStar_Syntax_Syntax.flags = uu____5945}); FStar_Syntax_Syntax.pos = uu____5946; FStar_Syntax_Syntax.vars = uu____5947}) when (

let uu____5982 = (FStar_Ident.string_of_lid e)
in (Prims.op_Equality uu____5982 "FStar.HyperStack.ST.StackInline")) -> begin
(FStar_Extraction_ML_Syntax.StackInline)::[]
end
| uu____5986 -> begin
[]
end))
in (

let meta = (FStar_List.append flags (FStar_List.append flags' flags''))
in (

let ml_lb1 = (

let uu___914_5991 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = uu___914_5991.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = uu___914_5991.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___914_5991.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___914_5991.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu___914_5991.FStar_Extraction_ML_Syntax.print_typ})
in (

let uu____5992 = (

let uu____5997 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___8_6004 -> (match (uu___8_6004) with
| FStar_Syntax_Syntax.Projector (uu____6006) -> begin
true
end
| uu____6012 -> begin
false
end))))
in (match (uu____5997) with
| true -> begin
(

let mname = (

let uu____6028 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____6028 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____6037 = (

let uu____6045 = (FStar_Util.right lbname)
in (

let uu____6046 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____6045 mname uu____6046 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____6037) with
| (env1, uu____6053, uu____6054) -> begin
((env1), ((

let uu___927_6058 = ml_lb1
in {FStar_Extraction_ML_Syntax.mllb_name = (FStar_Pervasives_Native.snd mname); FStar_Extraction_ML_Syntax.mllb_tysc = uu___927_6058.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___927_6058.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___927_6058.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = uu___927_6058.FStar_Extraction_ML_Syntax.mllb_meta; FStar_Extraction_ML_Syntax.print_typ = uu___927_6058.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____6063 -> begin
(

let uu____6065 = (

let uu____6073 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____6073 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (match (uu____6065) with
| (env1, uu____6080, uu____6081) -> begin
((env1), (ml_lb1))
end))
end))
in (match (uu____5992) with
| (g1, ml_lb2) -> begin
((g1), ((ml_lb2)::ml_lbs))
end))))))
end))
end)) ((g), ([])) bindings (FStar_Pervasives_Native.snd lbs1))
in (match (uu____5830) with
| (g1, ml_lbs') -> begin
(

let uu____6111 = (

let uu____6114 = (

let uu____6117 = (

let uu____6118 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____6118))
in (uu____6117)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.rev ml_lbs')))))::[])
in (

let uu____6121 = (maybe_register_plugin g1 se)
in (FStar_List.append uu____6114 uu____6121)))
in ((g1), (uu____6111)))
end))))
end
| uu____6126 -> begin
(

let uu____6127 = (

let uu____6129 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____6129))
in (failwith uu____6127))
end)
end))))
end))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____6139, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____6144 = ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) && (

let uu____6150 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (not (uu____6150))))
in (match (uu____6144) with
| true -> begin
(

let always_fail1 = (

let uu___947_6160 = se
in (

let uu____6161 = (

let uu____6162 = (

let uu____6169 = (

let uu____6170 = (

let uu____6173 = (always_fail lid t)
in (uu____6173)::[])
in ((false), (uu____6170)))
in ((uu____6169), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____6162))
in {FStar_Syntax_Syntax.sigel = uu____6161; FStar_Syntax_Syntax.sigrng = uu___947_6160.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___947_6160.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___947_6160.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___947_6160.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___947_6160.FStar_Syntax_Syntax.sigopts}))
in (

let uu____6180 = (extract_sig g always_fail1)
in (match (uu____6180) with
| (g1, mlm) -> begin
(

let uu____6199 = (FStar_Util.find_map quals (fun uu___9_6204 -> (match (uu___9_6204) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____6208 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____6199) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____6216 = (

let uu____6219 = (

let uu____6220 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____6220))
in (

let uu____6221 = (

let uu____6224 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____6224)::[])
in (uu____6219)::uu____6221))
in ((g1), (uu____6216)))
end
| uu____6227 -> begin
(

let uu____6230 = (FStar_Util.find_map quals (fun uu___10_6236 -> (match (uu___10_6236) with
| FStar_Syntax_Syntax.Projector (l, uu____6240) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____6241 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____6230) with
| FStar_Pervasives_Native.Some (uu____6248) -> begin
((g1), ([]))
end
| uu____6251 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____6256 -> begin
((g), ([]))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____6261 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____6261) with
| (ml_main, uu____6275, uu____6276) -> begin
(

let uu____6277 = (

let uu____6280 = (

let uu____6281 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____6281))
in (uu____6280)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____6277)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____6284) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____6293) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____6296) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng);
((g), ([]));
)
end);
))


let extract' : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option) = (fun g m -> (

let uu____6338 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___988_6342 = g
in (

let uu____6343 = (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name)
in {FStar_Extraction_ML_UEnv.env_tcenv = uu____6343; FStar_Extraction_ML_UEnv.env_bindings = uu___988_6342.FStar_Extraction_ML_UEnv.env_bindings; FStar_Extraction_ML_UEnv.env_mlident_map = uu___988_6342.FStar_Extraction_ML_UEnv.env_mlident_map; FStar_Extraction_ML_UEnv.tydefs = uu___988_6342.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___988_6342.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = name}))
in (

let uu____6344 = (FStar_Util.fold_map (fun g2 se -> (

let uu____6363 = (FStar_Options.debug_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____6363) with
| true -> begin
(

let nm = (

let uu____6374 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____6374 (FStar_String.concat ", ")))
in ((FStar_Util.print1 "+++About to extract {%s}\n" nm);
(

let uu____6391 = (FStar_Util.format1 "---Extracted {%s}" nm)
in (FStar_Util.measure_execution_time uu____6391 (fun uu____6401 -> (extract_sig g2 se))));
))
end
| uu____6402 -> begin
(extract_sig g2 se)
end))) g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____6344) with
| (g2, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____6423 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____6423 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin))))
in (match (((Prims.op_disEquality m.FStar_Syntax_Syntax.name.FStar_Ident.str "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface))))) with
| true -> begin
((

let uu____6438 = (

let uu____6440 = (FStar_Options.silent ())
in (not (uu____6440)))
in (match (uu____6438) with
| true -> begin
(

let uu____6443 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____6443))
end
| uu____6446 -> begin
()
end));
((g2), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLLib ((((name), (FStar_Pervasives_Native.Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))));
)
end
| uu____6496 -> begin
((g2), (FStar_Pervasives_Native.None))
end)))
end))))))


let extract : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option) = (fun g m -> ((

let uu____6518 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_left (fun a2 -> ()) uu____6518));
(

let uu____6521 = (

let uu____6523 = (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____6523)))
in (match (uu____6521) with
| true -> begin
(

let uu____6526 = (

let uu____6528 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (FStar_Util.format1 "Extract called on a module %s that should not be extracted" uu____6528))
in (failwith uu____6526))
end
| uu____6531 -> begin
()
end));
(

let uu____6533 = (FStar_Options.interactive ())
in (match (uu____6533) with
| true -> begin
((g), (FStar_Pervasives_Native.None))
end
| uu____6544 -> begin
(

let res = (

let uu____6553 = (FStar_Options.debug_any ())
in (match (uu____6553) with
| true -> begin
(

let msg = (

let uu____6564 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.format1 "Extracting module %s\n" uu____6564))
in (FStar_Util.measure_execution_time msg (fun uu____6574 -> (extract' g m))))
end
| uu____6575 -> begin
(extract' g m)
end))
in ((

let uu____6578 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_left (fun a3 -> ()) uu____6578));
res;
))
end));
))




