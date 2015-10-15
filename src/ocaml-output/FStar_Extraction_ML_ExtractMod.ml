
open Prims
let fail_exp = (fun lid t -> (let _128_16 = (let _128_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _128_14 = (let _128_13 = (FStar_Absyn_Syntax.targ t)
in (let _128_12 = (let _128_11 = (let _128_10 = (let _128_9 = (let _128_8 = (let _128_7 = (let _128_6 = (let _128_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _128_5))
in (FStar_Bytes.string_as_unicode_bytes _128_6))
in (_128_7, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Const_string (_128_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _128_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _128_10))
in (_128_11)::[])
in (_128_13)::_128_12))
in (_128_15, _128_14)))
in (FStar_Absyn_Syntax.mk_Exp_app _128_16 None FStar_Absyn_Syntax.dummyRange)))

let mangle_projector_lid = (fun x -> (let projecteeName = x.FStar_Absyn_Syntax.ident
in (let _63_11 = (FStar_Util.prefix x.FStar_Absyn_Syntax.ns)
in (match (_63_11) with
| (prefix, constrName) -> begin
(let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Absyn_Syntax.idText) "___") projecteeName.FStar_Absyn_Syntax.idText))
in (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

let rec extract_sig = (fun g se -> (let _63_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _128_25 = (let _128_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _128_24))
in (FStar_Util.print_string _128_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _63_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_63_32) with
| (c, tds) -> begin
(c, tds)
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _63_36, quals) -> begin
(let elet = (FStar_Absyn_Syntax.mk_Exp_let (lbs, FStar_Absyn_Const.exp_false_bool) None r)
in (let _63_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_63_46) with
| (ml_let, _63_43, _63_45) -> begin
(match (ml_let) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _63_49) -> begin
(let _63_78 = (FStar_List.fold_left2 (fun _63_54 ml_lb _63_62 -> (match ((_63_54, _63_62)) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _63_59; FStar_Absyn_Syntax.lbdef = _63_57}) -> begin
(let _63_75 = (match ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_1 -> (match (_63_1) with
| FStar_Absyn_Syntax.Projector (_63_65) -> begin
true
end
| _63_68 -> begin
false
end))))) with
| true -> begin
(let mname = (let _128_31 = (let _128_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _128_30))
in (FStar_All.pipe_right _128_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (let env = (let _128_34 = (let _128_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _128_32))
in (let _128_33 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_fv' env _128_34 mname _128_33 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit)))
in (env, (let _63_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _63_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _63_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _63_71.FStar_Extraction_ML_Syntax.mllb_def}))))
end
| false -> begin
(let _128_37 = (let _128_36 = (let _128_35 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_lb env lbname t _128_35 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit))
in (FStar_All.pipe_left Prims.fst _128_36))
in (_128_37, ml_lb))
end)
in (match (_63_75) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_63_78) with
| (g, ml_lbs') -> begin
(g, (FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
end))
end
| _63_80 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(match ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption))) with
| true -> begin
(let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _128_39 = (let _128_38 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in (bs, _128_38))
in (FStar_Absyn_Syntax.mk_Exp_abs _128_39 None FStar_Absyn_Syntax.dummyRange))
end
| _63_92 -> begin
(fail_exp lid t)
end)
in (let se = FStar_Absyn_Syntax.Sig_let (((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _63_97 = (extract_sig g se)
in (match (_63_97) with
| (g, mlm) -> begin
(let is_record = (FStar_Util.for_some (fun _63_2 -> (match (_63_2) with
| FStar_Absyn_Syntax.RecordType (_63_100) -> begin
true
end
| _63_103 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _63_3 -> (match (_63_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _63_109 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _128_43 = (let _128_42 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_128_42)::[])
in (g, _128_43))
end
| _63_113 -> begin
(match ((FStar_Util.find_map quals (fun _63_4 -> (match (_63_4) with
| FStar_Absyn_Syntax.Projector (l, _63_117) -> begin
Some (l)
end
| _63_121 -> begin
None
end)))) with
| Some (_63_123) -> begin
(g, [])
end
| _63_126 -> begin
(g, mlm)
end)
end))
end))))
end
| false -> begin
(g, [])
end)
end
| FStar_Absyn_Syntax.Sig_main (e, _63_129) -> begin
(let _63_137 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_63_137) with
| (ml_main, _63_134, _63_136) -> begin
(g, (FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

let extract_iface = (fun g m -> (let _128_49 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _128_49 Prims.fst)))

let rec extract = (fun g m -> (let _63_160 = (FStar_Absyn_Util.reset_gensym ())
in (let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (let g = (let _63_163 = g
in {FStar_Extraction_ML_Env.tcenv = _63_163.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _63_163.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _63_163.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in (match ((((m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (let _128_54 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str _128_54)))) with
| true -> begin
(let g = (extract_iface g m)
in (g, []))
end
| false -> begin
(let _63_169 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_63_169) with
| (g, sigs) -> begin
(let mlm = (FStar_List.flatten sigs)
in (let _128_59 = (let _128_58 = (let _128_57 = (let _128_56 = (let _128_55 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_128_55, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_128_56)::[])
in FStar_Extraction_ML_Syntax.MLLib (_128_57))
in (_128_58)::[])
in (g, _128_59)))
end))
end)))))
