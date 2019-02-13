
open Prims
open FStar_Pervasives

type env_t =
FStar_Extraction_ML_UEnv.uenv


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

let uu____97 = (

let uu____99 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" uu____99))
in ((uu____97), (FStar_Range.dummyRange)))
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

let uu____171 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____171) with
| ([], t1) -> begin
(

let b = (

let uu____214 = (FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____214))
in (

let uu____222 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs ((b)::[]) uu____222 FStar_Pervasives_Native.None)))
end
| (bs, t1) -> begin
(

let uu____259 = (fail_exp lid t1)
in (FStar_Syntax_Util.abs bs uu____259 FStar_Pervasives_Native.None))
end))
in (

let lb = (

let uu____263 = (

let uu____268 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____268))
in {FStar_Syntax_Syntax.lbname = uu____263; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = imp.FStar_Syntax_Syntax.pos})
in lb)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> x)


let lident_as_mlsymbol : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun id1 -> (FStar_Extraction_ML_Syntax.avoid_keyword id1.FStar_Ident.ident.FStar_Ident.idText))


let as_pair : 'Auu____290 . 'Auu____290 Prims.list  ->  ('Auu____290 * 'Auu____290) = (fun uu___405_301 -> (match (uu___405_301) with
| (a)::(b)::[] -> begin
((a), (b))
end
| uu____306 -> begin
(failwith "Expected a list with 2 elements")
end))


let flag_of_qual : FStar_Syntax_Syntax.qualifier  ->  FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option = (fun uu___406_321 -> (match (uu___406_321) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Assumed)
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.NoExtract)
end
| uu____324 -> begin
FStar_Pervasives_Native.None
end))


let rec extract_meta : FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option = (fun x -> (

let uu____333 = (FStar_Syntax_Subst.compress x)
in (match (uu____333) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____337; FStar_Syntax_Syntax.vars = uu____338} -> begin
(

let uu____341 = (

let uu____343 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____343))
in (match (uu____341) with
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
| uu____352 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____355; FStar_Syntax_Syntax.vars = uu____356}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____358)); FStar_Syntax_Syntax.pos = uu____359; FStar_Syntax_Syntax.vars = uu____360}, uu____361))::[]); FStar_Syntax_Syntax.pos = uu____362; FStar_Syntax_Syntax.vars = uu____363} -> begin
(

let uu____406 = (

let uu____408 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____408))
in (match (uu____406) with
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
| uu____417 -> begin
FStar_Pervasives_Native.None
end))
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("KremlinPrivate", uu____419)); FStar_Syntax_Syntax.pos = uu____420; FStar_Syntax_Syntax.vars = uu____421} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Private)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("c_inline", uu____426)); FStar_Syntax_Syntax.pos = uu____427; FStar_Syntax_Syntax.vars = uu____428} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.CInline)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ("substitute", uu____433)); FStar_Syntax_Syntax.pos = uu____434; FStar_Syntax_Syntax.vars = uu____435} -> begin
FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Substitute)
end
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____441); FStar_Syntax_Syntax.pos = uu____442; FStar_Syntax_Syntax.vars = uu____443} -> begin
(extract_meta x1)
end
| uu____450 -> begin
FStar_Pervasives_Native.None
end)))


let extract_metadata : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Extraction_ML_Syntax.meta Prims.list = (fun metas -> (FStar_List.choose extract_meta metas))


let binders_as_mlty_binders : 'Auu____470 . FStar_Extraction_ML_UEnv.uenv  ->  (FStar_Syntax_Syntax.bv * 'Auu____470) Prims.list  ->  (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list) = (fun env bs -> (FStar_Util.fold_map (fun env1 uu____512 -> (match (uu____512) with
| (bv, uu____523) -> begin
(

let uu____524 = (

let uu____525 = (

let uu____528 = (

let uu____529 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (uu____529))
in FStar_Pervasives_Native.Some (uu____528))
in (FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____525))
in (

let uu____531 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((uu____524), (uu____531))))
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

let uu____732 = (FStar_Syntax_Print.lid_to_string i.iname)
in (

let uu____734 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (

let uu____737 = (FStar_Syntax_Print.term_to_string i.ityp)
in (

let uu____739 = (

let uu____741 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (

let uu____755 = (FStar_Syntax_Print.lid_to_string d.dname)
in (

let uu____757 = (

let uu____759 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " uu____759))
in (Prims.strcat uu____755 uu____757))))))
in (FStar_All.pipe_right uu____741 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____732 uu____734 uu____737 uu____739))))))


let bundle_as_inductive_families : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.attribute Prims.list  ->  (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list) = (fun env ses quals attrs -> (

let uu____813 = (FStar_Util.fold_map (fun env1 se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas) -> begin
(

let uu____861 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____861) with
| (bs1, t1) -> begin
(

let datas1 = (FStar_All.pipe_right ses (FStar_List.collect (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (d, uu____900, t2, l', nparams, uu____904) when (FStar_Ident.lid_equals l l') -> begin
(

let uu____911 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____911) with
| (bs', body) -> begin
(

let uu____950 = (FStar_Util.first_N (FStar_List.length bs1) bs')
in (match (uu____950) with
| (bs_params, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____1041 uu____1042 -> (match (((uu____1041), (uu____1042))) with
| ((b', uu____1068), (b, uu____1070)) -> begin
(

let uu____1091 = (

let uu____1098 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (uu____1098)))
in FStar_Syntax_Syntax.NT (uu____1091))
end)) bs_params bs1)
in (

let t3 = (

let uu____1104 = (

let uu____1105 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest uu____1105))
in (FStar_All.pipe_right uu____1104 (FStar_Syntax_Subst.subst subst1)))
in ({dname = d; dtyp = t3})::[]))
end))
end))
end
| uu____1108 -> begin
[]
end))))
in (

let metadata = (

let uu____1112 = (extract_metadata (FStar_List.append se.FStar_Syntax_Syntax.sigattrs attrs))
in (

let uu____1115 = (FStar_List.choose flag_of_qual quals)
in (FStar_List.append uu____1112 uu____1115)))
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let env2 = (FStar_Extraction_ML_UEnv.extend_type_name env1 fv)
in ((env2), (({ifv = fv; iname = l; iparams = bs1; ityp = t1; idatas = datas1; iquals = se.FStar_Syntax_Syntax.sigquals; imetadata = metadata})::[]))))))
end))
end
| uu____1122 -> begin
((env1), ([]))
end)) env ses)
in (match (uu____813) with
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

let uu___416_1302 = empty_iface
in {iface_module_name = uu___416_1302.iface_module_name; iface_bindings = fvs; iface_tydefs = uu___416_1302.iface_tydefs; iface_type_names = uu___416_1302.iface_type_names}))


let iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list  ->  iface = (fun tds -> (

let uu___417_1313 = empty_iface
in (

let uu____1314 = (FStar_List.map (fun td -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds)
in {iface_module_name = uu___417_1313.iface_module_name; iface_bindings = uu___417_1313.iface_bindings; iface_tydefs = tds; iface_type_names = uu____1314})))


let iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list  ->  iface = (fun fvs -> (

let uu___418_1329 = empty_iface
in {iface_module_name = uu___418_1329.iface_module_name; iface_bindings = uu___418_1329.iface_bindings; iface_tydefs = uu___418_1329.iface_tydefs; iface_type_names = fvs}))


let iface_union : iface  ->  iface  ->  iface = (fun if1 if2 -> (

let uu____1341 = (match ((Prims.op_disEquality if1.iface_module_name if1.iface_module_name)) with
| true -> begin
(failwith "Union not defined")
end
| uu____1344 -> begin
if1.iface_module_name
end)
in {iface_module_name = uu____1341; iface_bindings = (FStar_List.append if1.iface_bindings if2.iface_bindings); iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs); iface_type_names = (FStar_List.append if1.iface_type_names if2.iface_type_names)}))


let iface_union_l : iface Prims.list  ->  iface = (fun ifs -> (FStar_List.fold_right iface_union ifs empty_iface))


let mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.string = (fun p -> (FStar_String.concat ". " (FStar_List.append (FStar_Pervasives_Native.fst p) (((FStar_Pervasives_Native.snd p))::[]))))


let tscheme_to_string : 'Auu____1386 . FStar_Extraction_ML_Syntax.mlpath  ->  ('Auu____1386 * FStar_Extraction_ML_Syntax.mlty)  ->  Prims.string = (fun cm ts -> (FStar_Extraction_ML_Code.string_of_mlty cm (FStar_Pervasives_Native.snd ts)))


let print_exp_binding : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_UEnv.exp_binding  ->  Prims.string = (fun cm e -> (

let uu____1418 = (FStar_Extraction_ML_Code.string_of_mlexpr cm e.FStar_Extraction_ML_UEnv.exp_b_expr)
in (

let uu____1420 = (tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme)
in (

let uu____1422 = (FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok)
in (FStar_Util.format4 "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }" e.FStar_Extraction_ML_UEnv.exp_b_name uu____1418 uu____1420 uu____1422)))))


let print_binding : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)  ->  Prims.string = (fun cm uu____1440 -> (match (uu____1440) with
| (fv, exp_binding) -> begin
(

let uu____1448 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____1450 = (print_exp_binding cm exp_binding)
in (FStar_Util.format2 "(%s, %s)" uu____1448 uu____1450)))
end))


let print_tydef : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_UEnv.tydef  ->  Prims.string = (fun cm tydef -> (

let uu____1465 = (FStar_Syntax_Print.fv_to_string tydef.FStar_Extraction_ML_UEnv.tydef_fv)
in (

let uu____1467 = (tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def)
in (FStar_Util.format2 "(%s, %s)" uu____1465 uu____1467))))


let iface_to_string : iface  ->  Prims.string = (fun iface1 -> (

let cm = iface1.iface_module_name
in (

let print_type_name = (fun tn -> (FStar_Syntax_Print.fv_to_string tn))
in (

let uu____1485 = (

let uu____1487 = (FStar_List.map (print_binding cm) iface1.iface_bindings)
in (FStar_All.pipe_right uu____1487 (FStar_String.concat "\n")))
in (

let uu____1501 = (

let uu____1503 = (FStar_List.map (print_tydef cm) iface1.iface_tydefs)
in (FStar_All.pipe_right uu____1503 (FStar_String.concat "\n")))
in (

let uu____1513 = (

let uu____1515 = (FStar_List.map print_type_name iface1.iface_type_names)
in (FStar_All.pipe_right uu____1515 (FStar_String.concat "\n")))
in (FStar_Util.format4 "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}" (mlpath_to_string iface1.iface_module_name) uu____1485 uu____1501 uu____1513)))))))


let gamma_to_string : FStar_Extraction_ML_UEnv.uenv  ->  Prims.string = (fun env -> (

let cm = env.FStar_Extraction_ML_UEnv.currentModule
in (

let gamma = (FStar_List.collect (fun uu___407_1548 -> (match (uu___407_1548) with
| FStar_Extraction_ML_UEnv.Fv (b, e) -> begin
(((b), (e)))::[]
end
| uu____1565 -> begin
[]
end)) env.FStar_Extraction_ML_UEnv.env_bindings)
in (

let uu____1570 = (

let uu____1572 = (FStar_List.map (print_binding cm) gamma)
in (FStar_All.pipe_right uu____1572 (FStar_String.concat "\n")))
in (FStar_Util.format1 "Gamma = {\n %s }" uu____1570)))))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env quals attrs lb -> (

let uu____1632 = (

let uu____1641 = (FStar_TypeChecker_Env.open_universes_in env.FStar_Extraction_ML_UEnv.env_tcenv lb.FStar_Syntax_Syntax.lbunivs ((lb.FStar_Syntax_Syntax.lbdef)::(lb.FStar_Syntax_Syntax.lbtyp)::[]))
in (match (uu____1641) with
| (tcenv, uu____1659, def_typ) -> begin
(

let uu____1665 = (as_pair def_typ)
in ((tcenv), (uu____1665)))
end))
in (match (uu____1632) with
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

let uu____1696 = (

let uu____1697 = (FStar_Syntax_Subst.compress lbdef1)
in (FStar_All.pipe_right uu____1697 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right uu____1696 FStar_Syntax_Util.un_uinst))
in (

let def1 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____1705) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| uu____1724 -> begin
def
end)
in (

let uu____1725 = (match (def1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1736) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| uu____1761 -> begin
(([]), (def1))
end)
in (match (uu____1725) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun uu___408_1781 -> (match (uu___408_1781) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1784 -> begin
false
end)) quals)
in (

let uu____1786 = (binders_as_mlty_binders env bs)
in (match (uu____1786) with
| (env1, ml_bs) -> begin
(

let body1 = (

let uu____1813 = (FStar_Extraction_ML_Term.term_as_mlty env1 body)
in (FStar_All.pipe_right uu____1813 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env1))))
in (

let mangled_projector = (

let uu____1818 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___409_1825 -> (match (uu___409_1825) with
| FStar_Syntax_Syntax.Projector (uu____1827) -> begin
true
end
| uu____1833 -> begin
false
end))))
in (match (uu____1818) with
| true -> begin
(

let mname = (mangle_projector_lid lid)
in FStar_Pervasives_Native.Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____1841 -> begin
FStar_Pervasives_Native.None
end))
in (

let metadata = (

let uu____1847 = (extract_metadata attrs)
in (

let uu____1850 = (FStar_List.choose flag_of_qual quals)
in (FStar_List.append uu____1847 uu____1850)))
in (

let td = (

let uu____1873 = (lident_as_mlsymbol lid)
in ((assumed), (uu____1873), (mangled_projector), (ml_bs), (metadata), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body1)))))
in (

let def2 = (

let uu____1885 = (

let uu____1886 = (

let uu____1887 = (FStar_Ident.range_of_lid lid)
in (FStar_Extraction_ML_Util.mlloc_of_range uu____1887))
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____1886))
in (uu____1885)::(FStar_Extraction_ML_Syntax.MLM_Ty ((td)::[]))::[])
in (

let uu____1888 = (

let uu____1893 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___410_1899 -> (match (uu___410_1899) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____1903 -> begin
false
end))))
in (match (uu____1893) with
| true -> begin
(

let uu____1910 = (FStar_Extraction_ML_UEnv.extend_type_name env fv)
in ((uu____1910), ((iface_of_type_names ((fv)::[])))))
end
| uu____1911 -> begin
(

let uu____1913 = (FStar_Extraction_ML_UEnv.extend_tydef env fv td)
in (match (uu____1913) with
| (env2, tydef) -> begin
(

let uu____1924 = (iface_of_tydefs ((tydef)::[]))
in ((env2), (uu____1924)))
end))
end))
in (match (uu____1888) with
| (env2, iface1) -> begin
((env2), (iface1), (def2))
end)))))))
end)))
end))))))))
end)))


let extract_bundle_iface : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * iface) = (fun env se -> (

let extract_ctor = (fun env_iparams ml_tyvars env1 ctor -> (

let mlt = (

let uu____2000 = (FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2000))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____2007 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (match (uu____2007) with
| (env2, uu____2026, b) -> begin
((env2), (((fvv), (b))))
end))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____2065 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____2065) with
| (env_iparams, vars) -> begin
(

let uu____2093 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor env_iparams vars) env1))
in (match (uu____2093) with
| (env2, ctors) -> begin
((env2), (ctors))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____2157, t, uu____2159, uu____2160, uu____2161); FStar_Syntax_Syntax.sigrng = uu____2162; FStar_Syntax_Syntax.sigquals = uu____2163; FStar_Syntax_Syntax.sigmeta = uu____2164; FStar_Syntax_Syntax.sigattrs = uu____2165})::[], uu____2166), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____2185 = (extract_ctor env [] env {dname = l; dtyp = t})
in (match (uu____2185) with
| (env1, ctor) -> begin
((env1), ((iface_of_bindings ((ctor)::[]))))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____2218), quals) -> begin
(

let uu____2232 = (bundle_as_inductive_families env ses quals se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____2232) with
| (env1, ifams) -> begin
(

let uu____2249 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____2249) with
| (env2, td) -> begin
(

let uu____2290 = (

let uu____2291 = (

let uu____2292 = (FStar_List.map (fun x -> x.ifv) ifams)
in (iface_of_type_names uu____2292))
in (iface_union uu____2291 (iface_of_bindings (FStar_List.flatten td))))
in ((env2), (uu____2290)))
end))
end))
end
| uu____2301 -> begin
(failwith "Unexpected signature element")
end))))


let extract_type_declaration : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g lid quals attrs univs1 t -> (

let uu____2376 = (

let uu____2378 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___411_2384 -> (match (uu___411_2384) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2387 -> begin
false
end))))
in (not (uu____2378)))
in (match (uu____2376) with
| true -> begin
((g), (empty_iface), ([]))
end
| uu____2400 -> begin
(

let uu____2402 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2402) with
| (bs, uu____2426) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let lb = (

let uu____2449 = (FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit FStar_Pervasives_Native.None)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____2449; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = t.FStar_Syntax_Syntax.pos})
in (extract_typ_abbrev g quals attrs lb)))
end))
end)))


let extract_reifiable_effect : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Extraction_ML_UEnv.uenv * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g ed -> (

let extend_env = (fun g1 lid ml_name tm tysc -> (

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (

let uu____2512 = (FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false)
in (match (uu____2512) with
| (g2, mangled_name, exp_binding) -> begin
((

let uu____2534 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g2.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2534) with
| true -> begin
(FStar_Util.print1 "Mangled name: %s\n" mangled_name)
end
| uu____2540 -> begin
()
end));
(

let lb = {FStar_Extraction_ML_Syntax.mllb_name = mangled_name; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g2), ((iface_of_bindings ((((fv), (exp_binding)))::[]))), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ((lb)::[]))))));
)
end))))
in (

let rec extract_fv = (fun tm -> ((

let uu____2570 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2570) with
| true -> begin
(

let uu____2575 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "extract_fv term: %s\n" uu____2575))
end
| uu____2578 -> begin
()
end));
(

let uu____2580 = (

let uu____2581 = (FStar_Syntax_Subst.compress tm)
in uu____2581.FStar_Syntax_Syntax.n)
in (match (uu____2580) with
| FStar_Syntax_Syntax.Tm_uinst (tm1, uu____2589) -> begin
(extract_fv tm1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2596 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (match (uu____2596) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____2601; FStar_Extraction_ML_UEnv.exp_b_expr = uu____2602; FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2604} -> begin
(

let uu____2607 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((uu____2607), (tysc)))
end)))
end
| uu____2608 -> begin
(

let uu____2609 = (

let uu____2611 = (FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos)
in (

let uu____2613 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.format2 "(%s) Not an fv: %s" uu____2611 uu____2613)))
in (failwith uu____2609))
end));
))
in (

let extract_action = (fun g1 a -> ((

let uu____2641 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2641) with
| true -> begin
(

let uu____2646 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2648 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.print2 "Action type %s and term %s\n" uu____2646 uu____2648)))
end
| uu____2651 -> begin
()
end));
(

let uu____2653 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (uu____2653) with
| (a_nm, a_lid) -> begin
(

let lbname = (

let uu____2673 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)) FStar_Syntax_Syntax.tun)
in FStar_Util.Inl (uu____2673))
in (

let lb = (FStar_Syntax_Syntax.mk_lb ((lbname), (a.FStar_Syntax_Syntax.action_univs), (FStar_Parser_Const.effect_Tot_lid), (a.FStar_Syntax_Syntax.action_typ), (a.FStar_Syntax_Syntax.action_defn), ([]), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)))
in (

let lbs = ((false), ((lb)::[]))
in (

let action_lb = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (

let uu____2703 = (FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb)
in (match (uu____2703) with
| (a_let, uu____2719, ty) -> begin
((

let uu____2722 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2722) with
| true -> begin
(

let uu____2727 = (FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let)
in (FStar_Util.print1 "Extracted action term: %s\n" uu____2727))
end
| uu____2730 -> begin
()
end));
(

let uu____2732 = (match (a_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((uu____2755, (mllb)::[]), uu____2757) -> begin
(match (mllb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some (tysc) -> begin
((mllb.FStar_Extraction_ML_Syntax.mllb_def), (tysc))
end
| FStar_Pervasives_Native.None -> begin
(failwith "No type scheme")
end)
end
| uu____2797 -> begin
(failwith "Impossible")
end)
in (match (uu____2732) with
| (exp, tysc) -> begin
((

let uu____2835 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug g1.FStar_Extraction_ML_UEnv.env_tcenv) (FStar_Options.Other ("ExtractionReify")))
in (match (uu____2835) with
| true -> begin
((

let uu____2841 = (FStar_Extraction_ML_Code.string_of_mlty a_nm (FStar_Pervasives_Native.snd tysc))
in (FStar_Util.print1 "Extracted action type: %s\n" uu____2841));
(FStar_List.iter (fun x -> (FStar_Util.print1 "and binders: %s\n" x)) (FStar_Pervasives_Native.fst tysc));
)
end
| uu____2855 -> begin
()
end));
(

let uu____2857 = (extend_env g1 a_lid a_nm exp tysc)
in (match (uu____2857) with
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

let uu____2879 = (

let uu____2886 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (uu____2886) with
| (return_tm, ty_sc) -> begin
(

let uu____2903 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (uu____2903) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (uu____2879) with
| (g1, return_iface, return_decl) -> begin
(

let uu____2928 = (

let uu____2935 = (extract_fv (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (uu____2935) with
| (bind_tm, ty_sc) -> begin
(

let uu____2952 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (uu____2952) with
| (bind_nm, bind_lid) -> begin
(extend_env g1 bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (uu____2928) with
| (g2, bind_iface, bind_decl) -> begin
(

let uu____2977 = (FStar_Util.fold_map extract_action g2 ed.FStar_Syntax_Syntax.actions)
in (match (uu____2977) with
| (g3, actions) -> begin
(

let uu____3014 = (FStar_List.unzip actions)
in (match (uu____3014) with
| (actions_iface, actions1) -> begin
(

let uu____3041 = (iface_union_l ((return_iface)::(bind_iface)::actions_iface))
in ((g3), (uu____3041), ((return_decl)::(bind_decl)::actions1)))
end))
end))
end))
end))))))


let extract_sigelt_iface : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.uenv * iface) = (fun g se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____3063) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3072) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____3089) -> begin
(extract_bundle_iface g se)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____3108 = (extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs univs1 t)
in (match (uu____3108) with
| (env, iface1, uu____3123) -> begin
((env), (iface1))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____3129) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____3138 = (extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs lb)
in (match (uu____3138) with
| (env, iface1, uu____3153) -> begin
((env), (iface1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _univs, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____3164 = ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) && (

let uu____3170 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (not (uu____3170))))
in (match (uu____3164) with
| true -> begin
(

let uu____3177 = (

let uu____3188 = (

let uu____3189 = (

let uu____3192 = (always_fail lid t)
in (uu____3192)::[])
in ((false), (uu____3189)))
in (FStar_Extraction_ML_Term.extract_lb_iface g uu____3188))
in (match (uu____3177) with
| (g1, bindings) -> begin
((g1), ((iface_of_bindings bindings)))
end))
end
| uu____3215 -> begin
((g), (empty_iface))
end)))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____3218) -> begin
(

let uu____3223 = (FStar_Extraction_ML_Term.extract_lb_iface g lbs)
in (match (uu____3223) with
| (g1, bindings) -> begin
((g1), ((iface_of_bindings bindings)))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____3252) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____3253) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_assume (uu____3254) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____3261) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____3262) -> begin
((g), (empty_iface))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng);
((g), (empty_iface));
)
end
| FStar_Syntax_Syntax.Sig_splice (uu____3277) -> begin
(failwith "impossible: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____3290 = ((FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname) && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders))
in (match (uu____3290) with
| true -> begin
(

let uu____3303 = (extract_reifiable_effect g ed)
in (match (uu____3303) with
| (env, iface1, uu____3318) -> begin
((env), (iface1))
end))
end
| uu____3323 -> begin
((g), (empty_iface))
end))
end))


let extract_iface' : env_t  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.uenv * iface) = (fun g modul -> (

let uu____3340 = (FStar_Options.interactive ())
in (match (uu____3340) with
| true -> begin
((g), (empty_iface))
end
| uu____3347 -> begin
(

let uu____3349 = (FStar_Options.restore_cmd_line_options true)
in (

let decls = modul.FStar_Syntax_Syntax.declarations
in (

let iface1 = (

let uu___419_3353 = empty_iface
in {iface_module_name = g.FStar_Extraction_ML_UEnv.currentModule; iface_bindings = uu___419_3353.iface_bindings; iface_tydefs = uu___419_3353.iface_tydefs; iface_type_names = uu___419_3353.iface_type_names})
in (

let res = (FStar_List.fold_left (fun uu____3371 se -> (match (uu____3371) with
| (g1, iface2) -> begin
(

let uu____3383 = (extract_sigelt_iface g1 se)
in (match (uu____3383) with
| (g2, iface') -> begin
(

let uu____3394 = (iface_union iface2 iface')
in ((g2), (uu____3394)))
end))
end)) ((g), (iface1)) decls)
in ((

let uu____3396 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_left (fun a1 -> ()) uu____3396));
res;
)))))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.uenv * iface) = (fun g modul -> (

let uu____3413 = (FStar_Options.debug_any ())
in (match (uu____3413) with
| true -> begin
(

let uu____3420 = (FStar_Util.format1 "Extracted interface of %s" modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (FStar_Util.measure_execution_time uu____3420 (fun uu____3428 -> (extract_iface' g modul))))
end
| uu____3429 -> begin
(extract_iface' g modul)
end)))


let extend_with_iface : FStar_Extraction_ML_UEnv.uenv  ->  iface  ->  FStar_Extraction_ML_UEnv.uenv = (fun g iface1 -> (

let uu___420_3442 = g
in (

let uu____3443 = (

let uu____3446 = (FStar_List.map (fun _0_1 -> FStar_Extraction_ML_UEnv.Fv (_0_1)) iface1.iface_bindings)
in (FStar_List.append uu____3446 g.FStar_Extraction_ML_UEnv.env_bindings))
in {FStar_Extraction_ML_UEnv.env_tcenv = uu___420_3442.FStar_Extraction_ML_UEnv.env_tcenv; FStar_Extraction_ML_UEnv.env_bindings = uu____3443; FStar_Extraction_ML_UEnv.tydefs = (FStar_List.append iface1.iface_tydefs g.FStar_Extraction_ML_UEnv.tydefs); FStar_Extraction_ML_UEnv.type_names = (FStar_List.append iface1.iface_type_names g.FStar_Extraction_ML_UEnv.type_names); FStar_Extraction_ML_UEnv.currentModule = uu___420_3442.FStar_Extraction_ML_UEnv.currentModule})))


let extract_bundle : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun env_iparams ml_tyvars env1 ctor -> (

let mlt = (

let uu____3530 = (FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____3530))
in (

let steps = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]
in (

let names1 = (

let uu____3538 = (

let uu____3539 = (

let uu____3542 = (FStar_TypeChecker_Normalize.normalize steps env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp)
in (FStar_Syntax_Subst.compress uu____3542))
in uu____3539.FStar_Syntax_Syntax.n)
in (match (uu____3538) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____3547) -> begin
(FStar_List.map (fun uu____3580 -> (match (uu____3580) with
| ({FStar_Syntax_Syntax.ppname = ppname; FStar_Syntax_Syntax.index = uu____3589; FStar_Syntax_Syntax.sort = uu____3590}, uu____3591) -> begin
ppname.FStar_Ident.idText
end)) bs)
end
| uu____3599 -> begin
[]
end))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (

let uu____3607 = (FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false)
in (match (uu____3607) with
| (env2, uu____3634, uu____3635) -> begin
(

let uu____3638 = (

let uu____3651 = (lident_as_mlsymbol ctor.dname)
in (

let uu____3653 = (

let uu____3661 = (FStar_Extraction_ML_Util.argTypes mlt)
in (FStar_List.zip names1 uu____3661))
in ((uu____3651), (uu____3653))))
in ((env2), (uu____3638)))
end))))))))
in (

let extract_one_family = (fun env1 ind -> (

let uu____3722 = (binders_as_mlty_binders env1 ind.iparams)
in (match (uu____3722) with
| (env_iparams, vars) -> begin
(

let uu____3766 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor env_iparams vars) env1))
in (match (uu____3766) with
| (env2, ctors) -> begin
(

let uu____3873 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (uu____3873) with
| (indices, uu____3915) -> begin
(

let ml_params = (

let uu____3940 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i uu____3966 -> (

let uu____3974 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" uu____3974)))))
in (FStar_List.append vars uu____3940))
in (

let tbody = (

let uu____3979 = (FStar_Util.find_opt (fun uu___412_3984 -> (match (uu___412_3984) with
| FStar_Syntax_Syntax.RecordType (uu____3986) -> begin
true
end
| uu____3996 -> begin
false
end)) ind.iquals)
in (match (uu____3979) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.RecordType (ns, ids)) -> begin
(

let uu____4008 = (FStar_List.hd ctors)
in (match (uu____4008) with
| (uu____4033, c_ty) -> begin
(

let fields = (FStar_List.map2 (fun id1 uu____4077 -> (match (uu____4077) with
| (uu____4088, ty) -> begin
(

let lid = (FStar_Ident.lid_of_ids (FStar_List.append ns ((id1)::[])))
in (

let uu____4093 = (lident_as_mlsymbol lid)
in ((uu____4093), (ty))))
end)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields))
end))
end
| uu____4096 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end))
in (

let uu____4099 = (

let uu____4122 = (lident_as_mlsymbol ind.iname)
in ((false), (uu____4122), (FStar_Pervasives_Native.None), (ml_params), (ind.imetadata), (FStar_Pervasives_Native.Some (tbody))))
in ((env2), (uu____4099)))))
end))
end))
end)))
in (match (((se.FStar_Syntax_Syntax.sigel), (se.FStar_Syntax_Syntax.sigquals))) with
| (FStar_Syntax_Syntax.Sig_bundle (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (l, uu____4167, t, uu____4169, uu____4170, uu____4171); FStar_Syntax_Syntax.sigrng = uu____4172; FStar_Syntax_Syntax.sigquals = uu____4173; FStar_Syntax_Syntax.sigmeta = uu____4174; FStar_Syntax_Syntax.sigattrs = uu____4175})::[], uu____4176), (FStar_Syntax_Syntax.ExceptionConstructor)::[]) -> begin
(

let uu____4195 = (extract_ctor env [] env {dname = l; dtyp = t})
in (match (uu____4195) with
| (env1, ctor) -> begin
((env1), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| (FStar_Syntax_Syntax.Sig_bundle (ses, uu____4248), quals) -> begin
(

let uu____4262 = (bundle_as_inductive_families env ses quals se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____4262) with
| (env1, ifams) -> begin
(

let uu____4281 = (FStar_Util.fold_map extract_one_family env1 ifams)
in (match (uu____4281) with
| (env2, td) -> begin
((env2), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end))
end))
end
| uu____4390 -> begin
(failwith "Unexpected signature element")
end))))


let maybe_register_plugin : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Extraction_ML_Syntax.mlmodule1 Prims.list = (fun g se -> (

let w = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
in (

let plugin_with_arity = (fun attrs -> (FStar_Util.find_map attrs (fun t -> (

let uu____4448 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4448) with
| (head1, args) -> begin
(

let uu____4496 = (

let uu____4498 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr head1)
in (not (uu____4498)))
in (match (uu____4496) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4509 -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, uu____4517)); FStar_Syntax_Syntax.pos = uu____4518; FStar_Syntax_Syntax.vars = uu____4519}, uu____4520))::[] -> begin
(

let uu____4559 = (

let uu____4563 = (FStar_Util.int_of_string s)
in FStar_Pervasives_Native.Some (uu____4563))
in FStar_Pervasives_Native.Some (uu____4559))
end
| uu____4569 -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end)
end))
end)))))
in (

let uu____4584 = (

let uu____4586 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____4586 (FStar_Pervasives_Native.Some (FStar_Options.Plugin))))
in (match (uu____4584) with
| true -> begin
[]
end
| uu____4594 -> begin
(

let uu____4596 = (plugin_with_arity se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____4596) with
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

let uu____4638 = (

let uu____4639 = (FStar_Ident.string_of_lid fv_lid1)
in FStar_Extraction_ML_Syntax.MLC_String (uu____4639))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____4638))
in (

let uu____4641 = (FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t arity_opt ml_name_str)
in (match (uu____4641) with
| FStar_Pervasives_Native.Some (interp, nbe_interp, arity, plugin1) -> begin
(

let uu____4674 = (match (plugin1) with
| true -> begin
(("FStar_Tactics_Native.register_plugin"), ((interp)::(nbe_interp)::[]))
end
| uu____4694 -> begin
(("FStar_Tactics_Native.register_tactic"), ((interp)::[]))
end)
in (match (uu____4674) with
| (register, args) -> begin
(

let h = (

let uu____4711 = (

let uu____4712 = (

let uu____4713 = (FStar_Ident.lid_of_str register)
in (FStar_Extraction_ML_Syntax.mlpath_of_lident uu____4713))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____4712))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____4711))
in (

let arity1 = (

let uu____4715 = (

let uu____4716 = (

let uu____4728 = (FStar_Util.string_of_int arity)
in ((uu____4728), (FStar_Pervasives_Native.None)))
in FStar_Extraction_ML_Syntax.MLC_Int (uu____4716))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____4715))
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
| uu____4757 -> begin
[]
end)
end))
end)))))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____4785 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>> extract_sig %s \n" uu____4785))));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____4794) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4803) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4820) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) when (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname) -> begin
(

let uu____4837 = (extract_reifiable_effect g ed)
in (match (uu____4837) with
| (env, _iface, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_splice (uu____4861) -> begin
(failwith "impossible: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____4875) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) when (FStar_Extraction_ML_Term.is_arity g t) -> begin
(

let uu____4881 = (extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs univs1 t)
in (match (uu____4881) with
| (env, uu____4897, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____4906) when (FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp) -> begin
(

let uu____4915 = (extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs lb)
in (match (uu____4915) with
| (env, uu____4931, impl) -> begin
((env), (impl))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____4940) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____4951 = (

let uu____4960 = (FStar_Syntax_Util.extract_attr' FStar_Parser_Const.postprocess_extr_with attrs)
in (match (uu____4960) with
| FStar_Pervasives_Native.None -> begin
((attrs), (FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.Some (ats, ((tau, FStar_Pervasives_Native.None))::uu____4989) -> begin
((ats), (FStar_Pervasives_Native.Some (tau)))
end
| FStar_Pervasives_Native.Some (ats, args) -> begin
((FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng ((FStar_Errors.Warning_UnrecognizedAttribute), ("Ill-formed application of `postprocess_for_extraction_with`")));
((attrs), (FStar_Pervasives_Native.None));
)
end))
in (match (uu____4951) with
| (attrs1, post_tau) -> begin
(

let postprocess_lb = (fun tau lb -> (

let lbdef = (FStar_TypeChecker_Env.postprocess g.FStar_Extraction_ML_UEnv.env_tcenv tau lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___421_5075 = lb
in {FStar_Syntax_Syntax.lbname = uu___421_5075.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___421_5075.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___421_5075.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___421_5075.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___421_5075.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___421_5075.FStar_Syntax_Syntax.lbpos})))
in (

let lbs1 = (

let uu____5084 = (match (post_tau) with
| FStar_Pervasives_Native.Some (tau) -> begin
(FStar_List.map (postprocess_lb tau) (FStar_Pervasives_Native.snd lbs))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives_Native.snd lbs)
end)
in (((FStar_Pervasives_Native.fst lbs)), (uu____5084)))
in (

let uu____5102 = (

let uu____5109 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs1), (FStar_Syntax_Util.exp_false_bool)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (FStar_Extraction_ML_Term.term_as_mlexpr g uu____5109))
in (match (uu____5102) with
| (ml_let, uu____5126, uu____5127) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, bindings), uu____5136) -> begin
(

let flags1 = (FStar_List.choose flag_of_qual quals)
in (

let flags' = (extract_metadata attrs1)
in (

let uu____5153 = (FStar_List.fold_left2 (fun uu____5179 ml_lb uu____5181 -> (match (((uu____5179), (uu____5181))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu____5203; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____5205; FStar_Syntax_Syntax.lbdef = uu____5206; FStar_Syntax_Syntax.lbattrs = uu____5207; FStar_Syntax_Syntax.lbpos = uu____5208}) -> begin
(

let uu____5233 = (FStar_All.pipe_right ml_lb.FStar_Extraction_ML_Syntax.mllb_meta (FStar_List.contains FStar_Extraction_ML_Syntax.Erased))
in (match (uu____5233) with
| true -> begin
((env), (ml_lbs))
end
| uu____5247 -> begin
(

let lb_lid = (

let uu____5250 = (

let uu____5253 = (FStar_Util.right lbname)
in uu____5253.FStar_Syntax_Syntax.fv_name)
in uu____5250.FStar_Syntax_Syntax.v)
in (

let flags'' = (

let uu____5257 = (

let uu____5258 = (FStar_Syntax_Subst.compress t)
in uu____5258.FStar_Syntax_Syntax.n)
in (match (uu____5257) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5263, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5264; FStar_Syntax_Syntax.effect_name = e; FStar_Syntax_Syntax.result_typ = uu____5266; FStar_Syntax_Syntax.effect_args = uu____5267; FStar_Syntax_Syntax.flags = uu____5268}); FStar_Syntax_Syntax.pos = uu____5269; FStar_Syntax_Syntax.vars = uu____5270}) when (

let uu____5305 = (FStar_Ident.string_of_lid e)
in (Prims.op_Equality uu____5305 "FStar.HyperStack.ST.StackInline")) -> begin
(FStar_Extraction_ML_Syntax.StackInline)::[]
end
| uu____5309 -> begin
[]
end))
in (

let meta = (FStar_List.append flags1 (FStar_List.append flags' flags''))
in (

let ml_lb1 = (

let uu___422_5314 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = uu___422_5314.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = uu___422_5314.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___422_5314.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___422_5314.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = uu___422_5314.FStar_Extraction_ML_Syntax.print_typ})
in (

let uu____5315 = (

let uu____5320 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___413_5327 -> (match (uu___413_5327) with
| FStar_Syntax_Syntax.Projector (uu____5329) -> begin
true
end
| uu____5335 -> begin
false
end))))
in (match (uu____5320) with
| true -> begin
(

let mname = (

let uu____5351 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right uu____5351 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let uu____5360 = (

let uu____5368 = (FStar_Util.right lbname)
in (

let uu____5369 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env uu____5368 mname uu____5369 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (match (uu____5360) with
| (env1, uu____5376, uu____5377) -> begin
((env1), ((

let uu___423_5381 = ml_lb1
in {FStar_Extraction_ML_Syntax.mllb_name = (FStar_Pervasives_Native.snd mname); FStar_Extraction_ML_Syntax.mllb_tysc = uu___423_5381.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = uu___423_5381.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = uu___423_5381.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.mllb_meta = uu___423_5381.FStar_Extraction_ML_Syntax.mllb_meta; FStar_Extraction_ML_Syntax.print_typ = uu___423_5381.FStar_Extraction_ML_Syntax.print_typ})))
end)))
end
| uu____5386 -> begin
(

let uu____5388 = (

let uu____5396 = (FStar_Util.must ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t uu____5396 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (match (uu____5388) with
| (env1, uu____5403, uu____5404) -> begin
((env1), (ml_lb1))
end))
end))
in (match (uu____5315) with
| (g1, ml_lb2) -> begin
((g1), ((ml_lb2)::ml_lbs))
end))))))
end))
end)) ((g), ([])) bindings (FStar_Pervasives_Native.snd lbs1))
in (match (uu____5153) with
| (g1, ml_lbs') -> begin
(

let uu____5434 = (

let uu____5437 = (

let uu____5440 = (

let uu____5441 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____5441))
in (uu____5440)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ((FStar_List.rev ml_lbs')))))::[])
in (

let uu____5444 = (maybe_register_plugin g1 se)
in (FStar_List.append uu____5437 uu____5444)))
in ((g1), (uu____5434)))
end))))
end
| uu____5449 -> begin
(

let uu____5450 = (

let uu____5452 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" uu____5452))
in (failwith uu____5450))
end)
end))))
end))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____5462, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____5467 = ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) && (

let uu____5473 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (not (uu____5473))))
in (match (uu____5467) with
| true -> begin
(

let always_fail1 = (

let uu___424_5483 = se
in (

let uu____5484 = (

let uu____5485 = (

let uu____5492 = (

let uu____5493 = (

let uu____5496 = (always_fail lid t)
in (uu____5496)::[])
in ((false), (uu____5493)))
in ((uu____5492), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____5485))
in {FStar_Syntax_Syntax.sigel = uu____5484; FStar_Syntax_Syntax.sigrng = uu___424_5483.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___424_5483.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___424_5483.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___424_5483.FStar_Syntax_Syntax.sigattrs}))
in (

let uu____5503 = (extract_sig g always_fail1)
in (match (uu____5503) with
| (g1, mlm) -> begin
(

let uu____5522 = (FStar_Util.find_map quals (fun uu___414_5527 -> (match (uu___414_5527) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____5531 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____5522) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____5539 = (

let uu____5542 = (

let uu____5543 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____5543))
in (

let uu____5544 = (

let uu____5547 = (FStar_Extraction_ML_Term.ind_discriminator_body g1 lid l)
in (uu____5547)::[])
in (uu____5542)::uu____5544))
in ((g1), (uu____5539)))
end
| uu____5550 -> begin
(

let uu____5553 = (FStar_Util.find_map quals (fun uu___415_5559 -> (match (uu___415_5559) with
| FStar_Syntax_Syntax.Projector (l, uu____5563) -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____5564 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____5553) with
| FStar_Pervasives_Native.Some (uu____5571) -> begin
((g1), ([]))
end
| uu____5574 -> begin
((g1), (mlm))
end))
end))
end)))
end
| uu____5579 -> begin
((g), ([]))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____5584 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (uu____5584) with
| (ml_main, uu____5598, uu____5599) -> begin
(

let uu____5600 = (

let uu____5603 = (

let uu____5604 = (FStar_Extraction_ML_Util.mlloc_of_range se.FStar_Syntax_Syntax.sigrng)
in FStar_Extraction_ML_Syntax.MLM_Loc (uu____5604))
in (uu____5603)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (uu____5600)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____5607) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_assume (uu____5615) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____5624) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5627) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng);
((g), ([]));
)
end);
))


let extract' : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option) = (fun g m -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let uu____5670 = (FStar_Options.restore_cmd_line_options true)
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g1 = (

let uu___425_5674 = g
in (

let uu____5675 = (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name)
in {FStar_Extraction_ML_UEnv.env_tcenv = uu____5675; FStar_Extraction_ML_UEnv.env_bindings = uu___425_5674.FStar_Extraction_ML_UEnv.env_bindings; FStar_Extraction_ML_UEnv.tydefs = uu___425_5674.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___425_5674.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = name}))
in (

let uu____5676 = (FStar_Util.fold_map (fun g2 se -> (

let uu____5695 = (FStar_Options.debug_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____5695) with
| true -> begin
(

let nm = (

let uu____5706 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____5706 (FStar_String.concat ", ")))
in ((FStar_Util.print1 "+++About to extract {%s}\n" nm);
(

let uu____5723 = (FStar_Util.format1 "---Extracted {%s}" nm)
in (FStar_Util.measure_execution_time uu____5723 (fun uu____5733 -> (extract_sig g2 se))));
))
end
| uu____5734 -> begin
(extract_sig g2 se)
end))) g1 m.FStar_Syntax_Syntax.declarations)
in (match (uu____5676) with
| (g2, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in (

let is_kremlin = (

let uu____5755 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____5755 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin))))
in (match (((Prims.op_disEquality m.FStar_Syntax_Syntax.name.FStar_Ident.str "Prims") && (is_kremlin || (not (m.FStar_Syntax_Syntax.is_interface))))) with
| true -> begin
((

let uu____5770 = (

let uu____5772 = (FStar_Options.silent ())
in (not (uu____5772)))
in (match (uu____5770) with
| true -> begin
(

let uu____5775 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracted module %s\n" uu____5775))
end
| uu____5778 -> begin
()
end));
((g2), (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLLib ((((name), (FStar_Pervasives_Native.Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))));
)
end
| uu____5828 -> begin
((g2), (FStar_Pervasives_Native.None))
end)))
end)))));
))


let extract : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option) = (fun g m -> ((

let uu____5850 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_left (fun a2 -> ()) uu____5850));
(

let uu____5853 = (

let uu____5855 = (FStar_Options.should_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____5855)))
in (match (uu____5853) with
| true -> begin
(

let uu____5858 = (

let uu____5860 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (FStar_Util.format1 "Extract called on a module %s that should not be extracted" uu____5860))
in (failwith uu____5858))
end
| uu____5863 -> begin
()
end));
(

let uu____5865 = (FStar_Options.interactive ())
in (match (uu____5865) with
| true -> begin
((g), (FStar_Pervasives_Native.None))
end
| uu____5876 -> begin
(

let res = (

let uu____5885 = (FStar_Options.debug_any ())
in (match (uu____5885) with
| true -> begin
(

let msg = (

let uu____5896 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.format1 "Extracting module %s\n" uu____5896))
in (FStar_Util.measure_execution_time msg (fun uu____5906 -> (extract' g m))))
end
| uu____5907 -> begin
(extract' g m)
end))
in ((

let uu____5910 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_left (fun a3 -> ()) uu____5910));
res;
))
end));
))




