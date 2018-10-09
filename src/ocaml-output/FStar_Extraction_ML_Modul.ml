
open Prims
open FStar_Pervasives

type env_t =
FStar_Extraction_ML_UEnv.env


let fail_exp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun lid t -> (

let uu____13 = (

let uu____20 = (

let uu____21 = (

let uu____38 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____41 = (

let uu____52 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____61 = (

let uu____72 = (

let uu____81 = (

let uu____82 = (

let uu____89 = (

let uu____90 = (

let uu____91 = (

let uu____96 = (

let uu____97 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" uu____97))
in ((uu____96), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (uu____91))
in FStar_Syntax_Syntax.Tm_constant (uu____90))
in (FStar_Syntax_Syntax.mk uu____89))
in (uu____82 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____81))
in (uu____72)::[])
in (uu____52)::uu____61))
in ((uu____38), (uu____41))))
in FStar_Syntax_Syntax.Tm_app (uu____21))
in (FStar_Syntax_Syntax.mk uu____20))
in (uu____13 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let always_fail : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lid t -> (

let imp = (

let uu____165 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____165) with
| ([], t1) -> begin
(

let b = (

let uu____208 = (FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____208))
in (

let uu____215 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs ((b)::[]) uu____215 FStar_Pervasives_Native.None)))
end
| (bs, t1) -> begin
(

let uu____252 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____252 FStar_Pervasives_Native.None))
end))
in (

let lb = (

let uu____256 = (

let uu____261 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____261))
in {FStar_Syntax_Syntax.lbname = uu____256; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = imp.FStar_Syntax_Syntax.pos})
in lb)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun id1 -> (FStar_Extraction_ML_Syntax.avoid_keyword id1.FStar_Ident.ident.FStar_Ident.idText))


let as_pair : 'Auu____278 . 'Auu____278 Prims.list  ->  ('Auu____278 * 'Auu____278) = (fun uu___402_289 -> (match (uu___402_289) with
| (a)::(b)::[] -> begin
((a), (b))
end
| uu____294 -> begin
(failwith "Expected a list with 2 elements")
end))


let flag_of_qual : FStar_Syntax_Syntax.qualifier  ->  FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option = (fun uu___403_307 -> (match (uu___403_307) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____310 -> begin
FStar_Pervasives_Native.None
end))


let rec extract_meta : FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option = (fun x -> (

let uu____318 = (FStar_Syntax_Subst.compress x)
in (match (uu____318) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____322; FStar_Syntax_Syntax.vars = uu____323} -> begin
(

let uu____326 = (

let uu____327 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____327))
in (match (uu____326) with
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
| uu____330 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____332; FStar_Syntax_Syntax.vars = uu____333}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____335)); FStar_Syntax_Syntax.pos = uu____336; FStar_Syntax_Syntax.vars = uu____337}, uu____338))::[]); FStar_Syntax_Syntax.pos = uu____339; FStar_Syntax_Syntax.vars = uu____340} -> begin
(

let uu____381 = (

let uu____382 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____382))
in (match (uu____381) with
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
| uu____385 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("KremlinPrivate", uu____386)); FStar_Syntax_Syntax.pos = uu____387; FStar_Syntax_Syntax.vars = uu____388} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("c_inline", uu____391)); FStar_Syntax_Syntax.pos = uu____392; FStar_Syntax_Syntax.vars = uu____393} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CInline)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("substitute", uu____396)); FStar_Syntax_Syntax.pos = uu____397; FStar_Syntax_Syntax.vars = uu____398} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Substitute)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____402); FStar_Syntax_Syntax.pos = uu____403; FStar_Syntax_Syntax.vars = uu____404} -> begin
(extract_meta x1)
end
| uu____411 -> begin
FStar_Pervasives_Native.None
end)))


let extract_metadata : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Extraction_ML_Syntax.meta Prims.list = (fun metas -> (FStar_List.choose extract_meta metas))


let binders_as_mlty_binders : 'Auu____429 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____429) Prims.list  ->  (FStar_Extraction_ML_UEnv.env * Prims.string Prims.list) = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____469 -> (match (uu____469) with
| (bv, uu____479) -> begin
(

let uu____480 = (

let uu____481 = (

let uu____484 = (

let uu____485 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____485))
in FStar_Pervasives_Native.Some (uu____484))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____481))
in (

let uu____486 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____480), (uu____486))))
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

let uu____675 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____676 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____677 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____678 = (

let uu____679 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____690 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____691 = (

let uu____692 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " uu____692))
in (Prims.strcat uu____690 uu____691))))))
in (FStar_All.pipe_right uu____679 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____675 uu____676 uu____677 uu____678))))))


let bundle_as_inductive_families : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.attribute Prims.list  ->  (FStar_Extraction_ML_UEnv.env * inductive_family Prims.list) = (fun env ses quals attrs -> (

let uu____739 = (FStar_Util.fold_map (fun env1 se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas) -> begin
(

let uu____787 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____787) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____826, t2, l', nparams, uu____830) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____835 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____835) with
| (bs', body) -> begin
(

let uu____874 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____874) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____965 uu____966 -> (match (((uu____965), (uu____966))) with
| ((b', uu____992), (b, uu____994)) -> begin
(

let uu____1015 = (

let uu____1022 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____1022)))
in FStar_Syntax_Syntax.NT (uu____1015))
end)) bs_params bs1)
in (

let t3 = (

let uu____1028 = (

let uu____1029 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____1029))
in (FStar_All.pipe_right uu____1028 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____1032 -> begin
[]
end))))
in (

let metadata = (

let uu____1036 = (extract_metadata (FStar_List.append se.FStar_Syntax_Syntax.sigattrs attrs))
in (

let uu____1039 = (FStar_List.choose flag_of_qual quals)
in (FStar_List.append uu____1036 uu____1039)))
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let env2 = (FStar_Extraction_ML_UEnv.extend_type_name env1 fv)
in ((env2), (({ifv = fv; iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = se.FStar_Syntax_Syntax.sigquals; imetadata = metadata})::[]))))))
end))
end
| uu____1046 -> begin
((env1), ([]))
end)) env ses)
in (match (uu____739) with
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

let uu___413_1216 = empty_iface
in {iface_module_name = uu___413_1216.iface_module_name; iface_bindings = fvs; iface_tydefs = uu___413_1216.iface_tydefs; iface_type_names = uu___413_1216.iface_type_names}))


let iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list  ->  iface = (fun tds -> (

let uu___414_1226 = empty_iface
in {iface_module_name = uu___414_1226.iface_module_name; iface_bindings = uu___414_1226.iface_bindings; iface_tydefs = tds; iface_type_names = uu___414_1226.iface_type_names}))


let iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list  ->  iface = (fun fvs -> (

let uu___415_1236 = empty_iface
in {iface_module_name = uu___415_1236.iface_module_name; iface_bindings = uu___415_1236.iface_bindings; iface_tydefs = uu___415_1236.iface_tydefs; iface_type_names = fvs}))


let iface_union : iface  ->  iface  ->  iface = (fun if1 if2 -> (

let uu____1247 = (match ((Prims.op_disEquality if1.iface_module_name if1.iface_module_name)) with
| true -> begin
(failwith "Union not defined")
end
| uu____1248 -> begin
if1.iface_module_name
end)
in {iface_module_name = uu____1247; iface_bindings = (FStar_List.append if1.iface_bindings if2.iface_bindings); iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs); iface_type_names = (FStar_List.append if1.iface_type_names if2.iface_type_names)}))


let iface_union_l : iface Prims.list  ->  iface = (fun ifs -> (FStar_List.fold_right iface_union ifs empty_iface))


let mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.string = (fun p -> (FStar_String.concat ". " (FStar_List.append (FStar_Pervasives_Native.fst p) (((FStar_Pervasives_Native.snd p))::[]))))


let tscheme_to_string : 'Auu____1277 . FStar_Extraction_ML_Syntax.mlpath  ->  ('Auu____1277 * FStar_Extraction_ML_Syntax.mlty)  ->  Prims.string = (fun cm ts -> (FStar_Extraction_ML_Code.string_of_mlty cm (FStar_Pervasives_Native.snd ts)))


let print_exp_binding : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_UEnv.exp_binding  ->  Prims.string = (fun cm e -> (

let uu____1306 = (FStar_Extraction_ML_Code.string_of_mlexpr cm e.FStar_Extraction_ML_UEnv.exp_b_expr)
in (

let uu____1307 = (tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme)
in (

let uu____1308 = (FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok)
in (FStar_Util.format4 "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }" e.FStar_Extraction_ML_UEnv.exp_b_name uu____1306 uu____1307 uu____1308)))))


let print_binding : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)  ->  Prims.string = (fun cm uu____1322 -> (match (uu____1322) with
| (fv, exp_binding) -> begin
(

let uu____1329 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____1330 = (print_exp_binding cm exp_binding)
in (FStar_Util.format2 "(%s, %s)" uu____1329 uu____1330)))
end))


let print_tydef : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_UEnv.tydef  ->  Prims.string = (fun cm tydef -> (

let uu____1341 = (FStar_Syntax_Print.fv_to_string tydef.FStar_Extraction_ML_UEnv.tydef_fv)
in (

let uu____1342 = (tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def)
in (FStar_Util.format2 "(%s, %s)" uu____1341 uu____1342))))


let iface_to_string : iface  ->  Prims.string = (fun iface1 -> (

let cm = iface1.iface_module_name
in (

let print_type_name = (fun tn -> (FStar_Syntax_Print.fv_to_string tn))
in (

let uu____1355 = (

let uu____1356 = (FStar_List.map (print_binding cm) iface1.iface_bindings)
in (FStar_All.pipe_right uu____1356 (FStar_String.concat "\n")))
in (

let uu____1365 = (

let uu____1366 = (FStar_List.map (print_tydef cm) iface1.iface_tydefs)
in (FStar_All.pipe_right uu____1366 (FStar_String.concat "\n")))
in (

let uu____1371 = (

let uu____1372 = (FStar_List.map print_type_name iface1.iface_type_names)
in (FStar_All.pipe_right uu____1372 (FStar_String.concat "\n")))
in (FStar_Util.format4 "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}" (mlpath_to_string iface1.iface_module_name) uu____1355 uu____1365 uu____1371)))))))


let gamma_to_string : FStar_Extraction_ML_UEnv.env  ->  Prims.string = (fun env -> (

let cm = env.FStar_Extraction_ML_UEnv.currentModule
in (

let gamma = (FStar_List.collect (fun uu___404_1397 -> (match (uu___404_1397) with
| FStar_Extraction_ML_UEnv.Fv (b, e) -> begin
(((b), (e)))::[]
end
| uu____1414 -> begin
[]
end)) env.FStar_Extraction_ML_UEnv.gamma)
in (

let uu____1419 = (

let uu____1420 = (FStar_List.map (print_binding cm) gamma)
in (FStar_All.pipe_right uu____1420 (FStar_String.concat "\n")))
in (FStar_Util.format1 "Gamma = {\n %s }" uu____1419)))))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env quals attrs lb -> (

let uu____1473 = (

let uu____1482 = (FStar_TypeChecker_Env.open_universes_in env.FStar_Extraction_ML_UEnv.tcenv lb.FStar_Syntax_Syntax.lbunivs ((lb.FStar_Syntax_Syntax.lbdef)::(lb.FStar_Syntax_Syntax.lbtyp)::[]))
in (match (uu____1482) with
| (tcenv, uu____1500, def_typ) -> begin
(

let uu____1506 = (as_pair def_typ)
in ((tcenv), (uu____1506)))
end))
in (match (uu____1473) with
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

let uu____1537 = (

let uu____1538 = (FStar_Syntax_Subst.compress lbdef1)
in (FStar_All.pipe_right uu____1538 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____1537 FStar_Syntax_Util.un_uinst))
in (

let def1 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____1546) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| uu____1565 -> begin
def
end)
in (

let uu____1566 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1577) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____1602 -> begin
(([]), (def1))
end)
in (match (uu____1566) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___405_1621 -> (match (uu___405_1621) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1622 -> begin
false
end)) quals)
in (

let uu____1623 = (binders_as_mlty_binders env bs)
in (match (uu____1623) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____1647 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____1647 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____1651 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___406_1656 -> (match (uu___406_1656) with
| FStar_Syntax_Syntax.Projector (uu____1657) -> begin
true
end
| uu____1662 -> begin
false
end))))
in (match (uu____1651) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in FStar_Pervasives_Native.Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____1666 -> begin
FStar_Pervasives_Native.None
end))
in (

let metadata = (

let uu____1670 = (extract_metadata attrs)
in (

let uu____1673 = (FStar_List.choose flag_of_qual quals)
in (FStar_List.append uu____1670 uu____1673)))
in (

let td = (

let uu____1693 = (lident_as_mlsymbol lid)
in ((assumed), (uu____1693), (mangled_projector), (ml_bs), (metadata), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (

let def2 = (

let uu____1701 = (

let uu____1702 = (

let uu____1703 = (FStar_Ident.range_of_lid lid)
in (FStar_Extraction_ML_Util.mlloc_of_range uu____1703))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1702))
in (uu____1701)::(FStar_Extraction_ML_Syntax.MLM_Ty ((td)::[]))::[])
in (

let uu____1704 = (

let uu____1709 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___407_1713 -> (match (uu___407_1713) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____1714 -> begin
false
end))))
in (match (uu____1709) with
| true -> begin
(

let uu____1719 = (FStar_Extraction_ML_UEnv.extend_type_name env1 fv)
in ((uu____1719), ((iface_of_type_names ((fv)::[])))))
end
| uu____1720 -> begin
(

let uu____1721 = (FStar_Extraction_ML_UEnv.extend_tydef env1 fv td)
in (match (uu____1721) with
| (env2, tydef) -> begin
((env2), ((iface_of_tydefs ((tydef)::[]))))
end))
end))
in (match (uu____1704) with
| (env2, iface1) -> begin
((env2), (iface1), (def2))
end)))))))
end)))
end))))))))
end)))


let extract_bundle_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * iface) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env1 ctor -> (

let mlt = (

let uu____1799 = (FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1799))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____1806 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (match (uu____1806) with
| (env2, uu____1822, b) -> begin
((env2), (((fvv), (b))))
end))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____1859 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____1859) with
| (env2, vars) -> begin
(

let uu____1884 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env2))
in (match (uu____1884) with
| (env3, ctors) -> begin
((env3), (ctors))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____1948, t, uu____1950, uu____1951, uu____1952); FStar_Syntax_Syntax.sigrng = uu____1953; FStar_Syntax_Syntax.sigquals = uu____1954; FStar_Syntax_Syntax.sigmeta = uu____1955; FStar_Syntax_Syntax.sigattrs = uu____1956})::[], uu____1957), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____1974 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____1974) with
| (env1, ctor) -> begin
((env1), ((iface_of_bindings ((ctor)::[]))))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____2006), quals) -> begin
(

let uu____2020 = (bundle_as_inductive_families env ses quals se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____2020) with
| (env1, ifams) -> begin
(

let uu____2037 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____2037) with
| (env2, td) -> begin
(

let uu____2078 = (

let uu____2079 = (

let uu____2080 = (FStar_List.map (fun x -> x.ifv) ifams)
in (iface_of_type_names uu____2080))
in (iface_union uu____2079 (iface_of_bindings (FStar_List.flatten td))))
in ((env2), (uu____2078)))
end))
end))
end
| uu____2089 -> begin
(failwith "Unexpected signature element")
end))))


let extract_type_declaration : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g lid quals attrs univs1 t -> (

let uu____2162 = (

let uu____2163 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___408_2167 -> (match (uu___408_2167) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2168 -> begin
false
end))))
in (not (uu____2163)))
in (match (uu____2162) with
| true -> begin
((g), (empty_iface), ([]))
end
| uu____2179 -> begin
(

let uu____2180 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2180) with
| (bs, uu____2204) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let lb = (

let uu____2227 = (FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit FStar_Pervasives_Native.None)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____2227; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = t.FStar_Syntax_Syntax.pos})
in (extract_typ_abbrev g quals attrs lb)))
end))
end)))


let extract_reifiable_effect : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Extraction_ML_UEnv.env * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g ed -> (

let extend_env = (fun g1 lid ml_name tm tysc -> (

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (

let uu____2289 = (FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false)
in (match (uu____2289) with
| (g2, mangled_name, exp_binding) -> begin
((

let uu____2306 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g2.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2306) with
| true -> begin
(FStar_Util.print1 "Mangled name: %s\n" mangled_name)
end
| uu____2307 -> begin
()
end));
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), ((iface_of_bindings ((((fv), (exp_binding)))::[]))), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ((lb)::[]))))));
)
end))))
in (

let rec extract_fv = (fun tm -> ((

let uu____2330 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2330) with
| true -> begin
(

let uu____2331 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "extract_fv term: %s\n" uu____2331))
end
| uu____2332 -> begin
()
end));
(

let uu____2333 = (

let uu____2334 = (FStar_Syntax_Subst.compress tm)
in uu____2334.FStar_Syntax_Syntax.n)
in (match (uu____2333) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____2342) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2349 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (match (uu____2349) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____2354; FStar_Extraction_ML_UEnv.exp_b_expr = uu____2355; FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2357} -> begin
(

let uu____2358 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____2358), (tysc)))
end)))
end
| uu____2359 -> begin
(failwith "Not an fv")
end));
))
in (

let extract_action = (fun g1 a -> ((

let uu____2385 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2385) with
| true -> begin
(

let uu____2386 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2387 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.print2 "Action type %s and term %s\n" uu____2386 uu____2387)))
end
| uu____2388 -> begin
()
end));
(

let uu____2389 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____2389) with
| (a_nm, a_lid) -> begin
(

let lbname = (

let uu____2409 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)) FStar_Syntax_Syntax.tun)
in FStar_Util.Inl (uu____2409))
in (

let lb = (FStar_Syntax_Syntax.mk_lb ((lbname), (a.FStar_Syntax_Syntax.action_univs), (FStar_Parser_Const.effect_Tot_lid), (a.FStar_Syntax_Syntax.action_typ), (a.FStar_Syntax_Syntax.action_defn), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)))
in (

let lbs = ((false), ((lb)::[]))
in (

let action_lb = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (

let uu____2433 = (FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb)
in (match (uu____2433) with
| (a_let, uu____2449, ty) -> begin
((

let uu____2452 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2452) with
| true -> begin
(

let uu____2453 = (FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let)
in (FStar_Util.print1 "Extracted action term: %s\n" uu____2453))
end
| uu____2454 -> begin
()
end));
(

let uu____2455 = (match (a_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____2476, (mllb)::[]), uu____2478) -> begin
(match (mllb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some (tysc) -> begin
((mllb.FStar_Extraction_ML_Syntax.mllb_def), (tysc))
end
| FStar_Pervasives_Native.None -> begin
(failwith "No type scheme")
end)
end
| uu____2514 -> begin
(failwith "Impossible")
end)
in (match (uu____2455) with
| (exp, tysc) -> begin
((

let uu____2548 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2548) with
| true -> begin
((

let uu____2550 = (FStar_Extraction_ML_Code.string_of_mlty a_nm (FStar_Pervasives_Native.snd tysc))
in (FStar_Util.print1 "Extracted action type: %s\n" uu____2550));
(FStar_List.iter (fun x -> (FStar_Util.print1 "and binders: %s\n" x)) (FStar_Pervasives_Native.fst tysc));
)
end
| uu____2557 -> begin
()
end));
(

let uu____2558 = (extend_env g1 a_lid a_nm exp tysc)
in (match (uu____2558) with
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

let uu____2580 = (

let uu____2587 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____2587) with
| (return_tm, ty_sc) -> begin
(

let uu____2604 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____2604) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____2580) with
| (g1, return_iface, return_decl) -> begin
(

let uu____2628 = (

let uu____2635 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____2635) with
| (bind_tm, ty_sc) -> begin
(

let uu____2652 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____2652) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____2628) with
| (g2, bind_iface, bind_decl) -> begin
(

let uu____2676 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____2676) with
| (g3, actions) -> begin
(

let uu____2713 = (FStar_List.unzip actions)
in (match (uu____2713) with
| (actions_iface, actions1) -> begin
(

let uu____2740 = (iface_union_l ((return_iface)::(bind_iface)::actions_iface))
in ((g3), (uu____2740), ((return_decl)::(bind_decl)::actions1)))
end))
end))
end))
end))))))


let extract_sigelt_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * iface) = (fun g se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____2761) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2770) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____2787) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____2805 = (extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs univs1 t)
in (match (uu____2805) with
| (env, iface1, uu____2820) -> begin
((env), (iface1))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____2826) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____2833 = (extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs lb)
in (match (uu____2833) with
| (env, iface1, uu____2848) -> begin
((env), (iface1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _univs, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____2859 = ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) && (

let uu____2863 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.tcenv t)
in (not (uu____2863))))
in (match (uu____2859) with
| true -> begin
(

let uu____2868 = (

let uu____2879 = (

let uu____2880 = (

let uu____2883 = (always_fail lid t)
in (uu____2883)::[])
in ((false), (uu____2880)))
in (FStar_Extraction_ML_Term.extract_lb_iface g uu____2879))
in (match (uu____2868) with
| (g1, bindings) -> begin
((g1), ((iface_of_bindings bindings)))
end))
end
| uu____2904 -> begin
((g), (empty_iface))
end)))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2906) -> begin
(

let uu____2911 = (FStar_Extraction_ML_Term.extract_lb_iface g lbs)
in (match (uu____2911) with
| (g1, bindings) -> begin
((g1), ((iface_of_bindings bindings)))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____2940) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____2941) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_assume (uu____2942) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____2949) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2950) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng);
((g), (empty_iface));
)
end
| FStar_Syntax_Syntax.Sig_splice (uu____2965) -> begin
(failwith "impossible: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____2977 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.tcenv ed.FStar_Syntax_Syntax.mname)
in (match (uu____2977) with
| true -> begin
(

let uu____2982 = (extract_reifiable_effect g ed)
in (match (uu____2982) with
| (env, iface1, uu____2997) -> begin
((env), (iface1))
end))
end
| uu____3002 -> begin
((g), (empty_iface))
end))
end))


let extract_iface : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Extraction_ML_UEnv.env * iface) = (fun g modul -> (

let iface1 = (

let uu___416_3022 = empty_iface
in {iface_module_name = g.FStar_Extraction_ML_UEnv.currentModule; iface_bindings = uu___416_3022.iface_bindings; iface_tydefs = uu___416_3022.iface_tydefs; iface_type_names = uu___416_3022.iface_type_names})
in (FStar_List.fold_left (fun uu____3035 se -> (match (uu____3035) with
| (g1, iface2) -> begin
(

let uu____3047 = (extract_sigelt_iface g1 se)
in (match (uu____3047) with
| (g2, iface') -> begin
(

let uu____3058 = (iface_union iface2 iface')
in ((g2), (uu____3058)))
end))
end)) ((g), (iface1)) modul)))


let extract_bundle : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env1 ctor -> (

let mlt = (

let uu____3124 = (FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1) uu____3124))
in (

let steps = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]
in (

let names1 = (

let uu____3131 = (

let uu____3132 = (

let uu____3135 = (FStar_TypeChecker_Normalize.normalize steps env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp)
in (FStar_Syntax_Subst.compress uu____3135))
in uu____3132.FStar_Syntax_Syntax.n)
in (match (uu____3131) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____3139) -> begin
(FStar_List.map (fun uu____3171 -> (match (uu____3171) with
| ({FStar_Syntax_Syntax.ppname = ppname; FStar_Syntax_Syntax.index = uu____3179; FStar_Syntax_Syntax.sort = uu____3180}, uu____3181) -> begin
ppname.FStar_Ident.idText
end)) bs)
end
| uu____3188 -> begin
[]
end))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____3195 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (match (uu____3195) with
| (env2, uu____3217, uu____3218) -> begin
(

let uu____3219 = (

let uu____3230 = (lident_as_mlsymbol ctor.dname)
in (

let uu____3231 = (

let uu____3238 = (FStar_Extraction_ML_Util.argTypes mlt)
in (FStar_List.zip names1 uu____3238))
in ((uu____3230), (uu____3231))))
in ((env2), (uu____3219)))
end))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____3290 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____3290) with
| (env2, vars) -> begin
(

let uu____3327 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env2))
in (match (uu____3327) with
| (env3, ctors) -> begin
(

let uu____3420 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____3420) with
| (indices, uu____3458) -> begin
(

let ml_params = (

let uu____3482 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____3505 -> (

let uu____3512 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____3512)))))
in (FStar_List.append vars uu____3482))
in (

let tbody = (

let uu____3514 = (FStar_Util.find_opt (fun uu___409_3519 -> (match (uu___409_3519) with
| FStar_Syntax_Syntax.RecordType (uu____3520) -> begin
true
end
| uu____3529 -> begin
false
end)) ind.iquals)
in (match (uu____3514) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____3540 = (FStar_List.hd ctors)
in (match (uu____3540) with
| (uu____3561, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id1 uu____3598 -> (match (uu____3598) with
| (uu____3607, ty) -> begin
(

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id1)::[])))
in (

let uu____3610 = (lident_as_mlsymbol lid)
in ((uu____3610), (ty))))
end)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____3611 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____3614 = (

let uu____3633 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____3633), (FStar_Pervasives_Native.None), (ml_params), (ind.imetadata), (FStar_Pervasives_Native.Some (tbody))))
in ((env3), (uu____3614)))))
end))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____3667, t, uu____3669, uu____3670, uu____3671); FStar_Syntax_Syntax.sigrng = uu____3672; FStar_Syntax_Syntax.sigquals = uu____3673; FStar_Syntax_Syntax.sigmeta = uu____3674; FStar_Syntax_Syntax.sigattrs = uu____3675})::[], uu____3676), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____3693 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (uu____3693) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____3739), quals) -> begin
(

let uu____3753 = (bundle_as_inductive_families env ses quals se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____3753) with
| (env1, ifams) -> begin
(

let uu____3772 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____3772) with
| (env2, td) -> begin
((env2), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end))
end))
end
| uu____3865 -> begin
(failwith "Unexpected signature element")
end))))


let maybe_register_plugin : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Extraction_ML_Syntax.mlmodule1 Prims.list = (fun g se -> (

let w = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
in (

let plugin_with_arity = (fun attrs -> (FStar_Util.find_map attrs (fun t -> (

let uu____3919 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3919) with
| (head1, args) -> begin
(

let uu____3966 = (

let uu____3967 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr head1)
in (not (uu____3967)))
in (match (uu____3966) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3974 -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, uu____3980)); FStar_Syntax_Syntax.pos = uu____3981; FStar_Syntax_Syntax.vars = uu____3982}, uu____3983))::[] -> begin
(

let uu____4020 = (

let uu____4023 = (FStar_Util.int_of_string s)
in FStar_Pervasives_Native.Some (uu____4023))
in FStar_Pervasives_Native.Some (uu____4020))
end
| uu____4026 -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end)
end))
end)))))
in (

let uu____4039 = (

let uu____4040 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____4040 (FStar_Pervasives_Native.Some (FStar_Options.Plugin))))
in (match (uu____4039) with
| true -> begin
[]
end
| uu____4047 -> begin
(

let uu____4048 = (plugin_with_arity se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____4048) with
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

let uu____4086 = (

let uu____4087 = (FStar_Ident.string_of_lid fv_lid1)
in FStar_Extraction_ML_Syntax.MLC_String (uu____4087))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____4086))
in (

let uu____4088 = (FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g.FStar_Extraction_ML_UEnv.tcenv fv fv_t arity_opt ml_name_str)
in (match (uu____4088) with
| FStar_Pervasives_Native.Some (interp, nbe_interp, arity, plugin1) -> begin
(

let uu____4113 = (match (plugin1) with
| true -> begin
(("FStar_Tactics_Native.register_plugin"), ((interp)::(nbe_interp)::[]))
end
| uu____4128 -> begin
(("FStar_Tactics_Native.register_tactic"), ((interp)::[]))
end)
in (match (uu____4113) with
| (register, args) -> begin
(

let h = (

let uu____4140 = (

let uu____4141 = (

let uu____4142 = (FStar_Ident.lid_of_str register)
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____4142))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____4141))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____4140))
in (

let arity1 = (

let uu____4144 = (

let uu____4145 = (

let uu____4156 = (FStar_Util.string_of_int arity)
in ((uu____4156), (FStar_Pervasives_Native.None)))
in FStar_Extraction_ML_Syntax.MLC_Int (uu____4145))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____4144))
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
| uu____4180 -> begin
[]
end)
end))
end)))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____4207 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____4207))));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____4214) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4223) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4240) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) when (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.tcenv ed.FStar_Syntax_Syntax.mname) -> begin
(

let uu____4256 = (extract_reifiable_effect g ed)
in (match (uu____4256) with
| (env, _iface, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_splice (uu____4280) -> begin
(failwith "impossible: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____4293) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____4299 = (extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs univs1 t)
in (match (uu____4299) with
| (env, uu____4315, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____4324) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____4331 = (extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs lb)
in (match (uu____4331) with
| (env, uu____4347, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____4356) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____4367 = (

let uu____4376 = (FStar_Syntax_Util.extract_attr' FStar_Parser_Const.postprocess_extr_with attrs)
in (match (uu____4376) with
| FStar_Pervasives_Native.None -> begin
((attrs), (FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.Some (ats, ((tau, FStar_Pervasives_Native.None))::uu____4405) -> begin
((ats), (FStar_Pervasives_Native.Some (tau)))
end
| FStar_Pervasives_Native.Some (ats, args) -> begin
((FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng ((FStar_Errors.Warning_UnrecognizedAttribute), ("Ill-formed application of `postprocess_for_extraction_with`")));
((attrs), (FStar_Pervasives_Native.None));
)
end))
in (match (uu____4367) with
| (attrs1, post_tau) -> begin
(

let postprocess_lb = (fun tau lb -> (

let lbdef = (FStar_TypeChecker_Env.postprocess g.FStar_Extraction_ML_UEnv.tcenv tau lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___417_4489 = lb
in {FStar_Syntax_Syntax.lbname = uu___417_4489.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___417_4489.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___417_4489.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___417_4489.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___417_4489.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___417_4489.FStar_Syntax_Syntax.lbpos})))
in (

let lbs1 = (

let uu____4497 = (match (post_tau) with
| FStar_Pervasives_Native.Some (tau) -> begin
(FStar_List.map (postprocess_lb tau) (FStar_Pervasives_Native.snd lbs))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives_Native.snd lbs)
end)
in (((FStar_Pervasives_Native.fst lbs)), (uu____4497)))
in (

let uu____4511 = (

let uu____4518 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs1), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (FStar_Extraction_ML_Term.term_as_mlexpr g uu____4518))
in (match (uu____4511) with
| (ml_let, uu____4534, uu____4535) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, bindings), uu____4544) -> begin
(

let flags1 = (FStar_List.choose flag_of_qual quals)
in (

let flags' = (extract_metadata attrs1)
in (

let uu____4561 = (FStar_List.fold_left2 (fun uu____4587 ml_lb uu____4589 -> (match (((uu____4587), (uu____4589))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____4611; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____4613; FStar_Syntax_Syntax.lbdef = uu____4614; FStar_Syntax_Syntax.lbattrs = uu____4615; FStar_Syntax_Syntax.lbpos = uu____4616}) -> begin
(

let uu____4641 = (FStar_All.pipe_right ml_lb.FStar_Extraction_ML_Syntax.mllb_meta (FStar_List.contains FStar_Extraction_ML_Syntax.Erased))
in (match (uu____4641) with
| true -> begin
((env), (ml_lbs))
end
| uu____4652 -> begin
(

let lb_lid = (

let uu____4654 = (

let uu____4657 = (FStar_Util.right lbname)
in uu____4657.FStar_Syntax_Syntax.fv_name)
in uu____4654.FStar_Syntax_Syntax.v)
in (

let flags'' = (

let uu____4661 = (

let uu____4662 = (FStar_Syntax_Subst.compress t)
in uu____4662.FStar_Syntax_Syntax.n)
in (match (uu____4661) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4667, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____4668; FStar_Syntax_Syntax.effect_name = e; FStar_Syntax_Syntax.result_typ = uu____4670; FStar_Syntax_Syntax.effect_args = uu____4671; FStar_Syntax_Syntax.flags = uu____4672}); FStar_Syntax_Syntax.pos = uu____4673; FStar_Syntax_Syntax.vars = uu____4674}) when (

let uu____4709 = (FStar_Ident.string_of_lid e)
in (Prims.op_Equality uu____4709 "FStar.HyperStack.ST.StackInline")) -> begin
(FStar_Extraction_ML_Syntax.StackInline)::[]
end
| uu____4710 -> begin
[]
end))
in (

let meta = (FStar_List.append flags1 (FStar_List.append flags' flags''))
in (

let ml_lb1 = (

let uu___418_4715 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = uu___418_4715.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = uu___418_4715.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___418_4715.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___418_4715.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu___418_4715.FStar_Extraction_ML_Syntax.print_typ})
in (

let uu____4716 = (

let uu____4721 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___410_4726 -> (match (uu___410_4726) with
| FStar_Syntax_Syntax.Projector (uu____4727) -> begin
true
end
| uu____4732 -> begin
false
end))))
in (match (uu____4721) with
| true -> begin
(

let mname = (

let uu____4744 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____4744 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____4751 = (

let uu____4758 = (FStar_Util.right lbname)
in (

let uu____4759 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____4758 mname uu____4759 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____4751) with
| (env1, uu____4765, uu____4766) -> begin
((env1), ((

let uu___419_4768 = ml_lb1
in {FStar_Extraction_ML_Syntax.mllb_name = (FStar_Pervasives_Native.snd mname); FStar_Extraction_ML_Syntax.mllb_tysc = uu___419_4768.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___419_4768.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___419_4768.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = uu___419_4768.FStar_Extraction_ML_Syntax.mllb_meta; FStar_Extraction_ML_Syntax.print_typ = uu___419_4768.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____4771 -> begin
(

let uu____4772 = (

let uu____4779 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____4779 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (match (uu____4772) with
| (env1, uu____4785, uu____4786) -> begin
((env1), (ml_lb1))
end))
end))
in (match (uu____4716) with
| (g1, ml_lb2) -> begin
((g1), ((ml_lb2)::ml_lbs))
end))))))
end))
end)) ((g), ([])) bindings (FStar_Pervasives_Native.snd lbs1))
in (match (uu____4561) with
| (g1, ml_lbs') -> begin
(

let uu____4813 = (

let uu____4816 = (

let uu____4819 = (

let uu____4820 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____4820))
in (uu____4819)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.rev ml_lbs')))))::[])
in (

let uu____4823 = (maybe_register_plugin g1 se)
in (FStar_List.append uu____4816 uu____4823)))
in ((g1), (uu____4813)))
end))))
end
| uu____4828 -> begin
(

let uu____4829 = (

let uu____4830 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____4830))
in (failwith uu____4829))
end)
end))))
end))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____4838, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____4843 = ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) && (

let uu____4847 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.tcenv t)
in (not (uu____4847))))
in (match (uu____4843) with
| true -> begin
(

let always_fail1 = (

let uu___420_4855 = se
in (

let uu____4856 = (

let uu____4857 = (

let uu____4864 = (

let uu____4865 = (

let uu____4868 = (always_fail lid t)
in (uu____4868)::[])
in ((false), (uu____4865)))
in ((uu____4864), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____4857))
in {FStar_Syntax_Syntax.sigel = uu____4856; FStar_Syntax_Syntax.sigrng = uu___420_4855.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___420_4855.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___420_4855.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___420_4855.FStar_Syntax_Syntax.sigattrs}))
in (

let uu____4873 = (extract_sig g always_fail1)
in (match (uu____4873) with
| (g1, mlm) -> begin
(

let uu____4892 = (FStar_Util.find_map quals (fun uu___411_4897 -> (match (uu___411_4897) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____4901 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____4892) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____4909 = (

let uu____4912 = (

let uu____4913 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____4913))
in (

let uu____4914 = (

let uu____4917 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____4917)::[])
in (uu____4912)::uu____4914))
in ((g1), (uu____4909)))
end
| uu____4920 -> begin
(

let uu____4923 = (FStar_Util.find_map quals (fun uu___412_4929 -> (match (uu___412_4929) with
| FStar_Syntax_Syntax.Projector (l, uu____4933) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____4934 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____4923) with
| FStar_Pervasives_Native.Some (uu____4941) -> begin
((g1), ([]))
end
| uu____4944 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____4949 -> begin
((g), ([]))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____4953 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____4953) with
| (ml_main, uu____4967, uu____4968) -> begin
(

let uu____4969 = (

let uu____4972 = (

let uu____4973 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____4973))
in (uu____4972)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____4969)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____4976) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_assume (uu____4983) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____4992) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4995) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng);
((g), ([]));
)
end);
))


let extract' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____5037 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___421_5040 = g
in (

let uu____5041 = (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name)
in {FStar_Extraction_ML_UEnv.tcenv = uu____5041; FStar_Extraction_ML_UEnv.gamma = uu___421_5040.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = uu___421_5040.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___421_5040.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = name}))
in (

let uu____5042 = (

let uu____5043 = (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____5043)))
in (match (uu____5042) with
| true -> begin
(

let uu____5050 = (extract_iface g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____5050) with
| (g2, iface1) -> begin
((FStar_Extraction_ML_UEnv.debug g2 (fun uu____5066 -> (

let uu____5067 = (iface_to_string iface1)
in (FStar_Util.print_string uu____5067))));
((g2), ([]));
)
end))
end
| uu____5070 -> begin
(

let uu____5071 = (FStar_Util.fold_map extract_sig g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____5071) with
| (g2, sigs) -> begin
((FStar_Extraction_ML_UEnv.debug g2 (fun uu____5101 -> (

let uu____5102 = (gamma_to_string g2)
in (FStar_Util.print_string uu____5102))));
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____5105 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____5105 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin))))
in (match (((Prims.op_disEquality m.FStar_Syntax_Syntax.name.FStar_Ident.str "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface))))) with
| true -> begin
((

let uu____5117 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____5117));
((g2), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (FStar_Pervasives_Native.Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[]));
)
end
| uu____5166 -> begin
((g2), ([]))
end)));
)
end))
end)))));
))


let extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let uu____5185 = (FStar_Options.debug_any ())
in (match (uu____5185) with
| true -> begin
(

let msg = (

let uu____5193 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.format1 "Extracting module %s\n" uu____5193))
in (FStar_Util.measure_execution_time msg (fun uu____5201 -> (extract' g m))))
end
| uu____5202 -> begin
(extract' g m)
end)))




