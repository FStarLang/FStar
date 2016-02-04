
open Prims
let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _184_15 = (let _184_14 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _184_13 = (let _184_12 = (let _184_11 = (let _184_10 = (let _184_9 = (let _184_8 = (let _184_7 = (let _184_6 = (let _184_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _184_5))
in (FStar_Bytes.string_as_unicode_bytes _184_6))
in (_184_7, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_string (_184_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _184_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _184_10))
in (_184_11)::[])
in ((FStar_Absyn_Syntax.targ t))::_184_12)
in (_184_14, _184_13)))
in (FStar_Absyn_Syntax.mk_Exp_app _184_15 None FStar_Absyn_Syntax.dummyRange)))

let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (let projecteeName = x.FStar_Ident.ident
in (let _81_11 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_81_11) with
| (prefix, constrName) -> begin
(let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Ident.idText) "___") projecteeName.FStar_Ident.idText))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

let rec extract_sig : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (let _81_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _184_24 = (let _184_23 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _184_23))
in (FStar_Util.print_string _184_24))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _81_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_81_32) with
| (c, tds) -> begin
(c, tds)
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _81_36, quals) -> begin
(let elet = (FStar_Absyn_Syntax.mk_Exp_let (lbs, FStar_Absyn_Const.exp_false_bool) None r)
in (let _81_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_81_46) with
| (ml_let, _81_43, _81_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _81_49) -> begin
(let _81_78 = (FStar_List.fold_left2 (fun _81_54 ml_lb _81_62 -> (match ((_81_54, _81_62)) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _81_59; FStar_Absyn_Syntax.lbdef = _81_57}) -> begin
(let _81_75 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _81_1 -> (match (_81_1) with
| FStar_Absyn_Syntax.Projector (_81_65) -> begin
true
end
| _81_68 -> begin
false
end)))) then begin
(let mname = (let _184_30 = (let _184_29 = (FStar_Util.right lbname)
in (mangle_projector_lid _184_29))
in (FStar_All.pipe_right _184_30 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (let env = (let _184_32 = (let _184_31 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _184_31))
in (FStar_Extraction_ML_Env.extend_fv' env _184_32 mname ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (env, (let _81_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _81_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _81_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _81_71.FStar_Extraction_ML_Syntax.mllb_def}))))
end else begin
(let _184_34 = (let _184_33 = (FStar_Extraction_ML_Env.extend_lb env lbname t ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)
in (FStar_All.pipe_left Prims.fst _184_33))
in (_184_34, ml_lb))
end
in (match (_81_75) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_81_78) with
| (g, ml_lbs') -> begin
(g, (FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
end))
end
| _81_80 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _184_36 = (let _184_35 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in (bs, _184_35))
in (FStar_Absyn_Syntax.mk_Exp_abs _184_36 None FStar_Absyn_Syntax.dummyRange))
end
| _81_92 -> begin
(fail_exp lid t)
end)
in (let se = FStar_Absyn_Syntax.Sig_let (((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _81_97 = (extract_sig g se)
in (match (_81_97) with
| (g, mlm) -> begin
(let is_record = (FStar_Util.for_some (fun _81_2 -> (match (_81_2) with
| FStar_Absyn_Syntax.RecordType (_81_100) -> begin
true
end
| _81_103 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _81_3 -> (match (_81_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _81_109 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _184_40 = (let _184_39 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_184_39)::[])
in (g, _184_40))
end
| _81_113 -> begin
(match ((FStar_Util.find_map quals (fun _81_4 -> (match (_81_4) with
| FStar_Absyn_Syntax.Projector (l, _81_117) -> begin
Some (l)
end
| _81_121 -> begin
None
end)))) with
| Some (_81_123) -> begin
(g, [])
end
| _81_126 -> begin
(g, mlm)
end)
end))
end))))
end else begin
(g, [])
end
end
| FStar_Absyn_Syntax.Sig_main (e, _81_129) -> begin
(let _81_137 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_81_137) with
| (ml_main, _81_134, _81_136) -> begin
(g, (FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

let extract_iface : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Extraction_ML_Env.env = (fun g m -> (let _184_46 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _184_46 Prims.fst)))

let rec extract : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (let _81_160 = (FStar_Absyn_Util.reset_gensym ())
in (let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (let g = (let _81_163 = g
in {FStar_Extraction_ML_Env.tcenv = _81_163.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _81_163.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _81_163.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (let _184_51 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains m.FStar_Absyn_Syntax.name.FStar_Ident.str _184_51))) then begin
(let g = (extract_iface g m)
in (g, []))
end else begin
(let _81_169 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_81_169) with
| (g, sigs) -> begin
(let mlm = (FStar_List.flatten sigs)
in (let _184_56 = (let _184_55 = (let _184_54 = (let _184_53 = (let _184_52 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_184_52, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_184_53)::[])
in FStar_Extraction_ML_Syntax.MLLib (_184_54))
in (_184_55)::[])
in (g, _184_56)))
end))
end))))




