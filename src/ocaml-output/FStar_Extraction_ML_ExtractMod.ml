
open Prims
let fail_exp = (fun lid t -> (let _130_16 = (let _130_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _130_14 = (let _130_13 = (FStar_Absyn_Syntax.targ t)
in (let _130_12 = (let _130_11 = (let _130_10 = (let _130_9 = (let _130_8 = (let _130_7 = (let _130_6 = (let _130_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _130_5))
in (FStar_Bytes.string_as_unicode_bytes _130_6))
in (_130_7, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Const_string (_130_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _130_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _130_10))
in (_130_11)::[])
in (_130_13)::_130_12))
in (_130_15, _130_14)))
in (FStar_Absyn_Syntax.mk_Exp_app _130_16 None FStar_Absyn_Syntax.dummyRange)))

let mangle_projector_lid = (fun x -> (let projecteeName = x.FStar_Absyn_Syntax.ident
in (let _64_11 = (FStar_Util.prefix x.FStar_Absyn_Syntax.ns)
in (match (_64_11) with
| (prefix, constrName) -> begin
(let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Absyn_Syntax.idText) "___") projecteeName.FStar_Absyn_Syntax.idText))
in (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

let rec extract_sig = (fun g se -> (let _64_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _130_25 = (let _130_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _130_24))
in (FStar_Util.print_string _130_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _64_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_64_32) with
| (c, tds) -> begin
(c, tds)
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _64_36, quals) -> begin
(let elet = (FStar_Absyn_Syntax.mk_Exp_let (lbs, FStar_Absyn_Const.exp_false_bool) None r)
in (let _64_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_64_46) with
| (ml_let, _64_43, _64_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _64_49) -> begin
(let _64_78 = (FStar_List.fold_left2 (fun _64_54 ml_lb _64_62 -> (match ((_64_54, _64_62)) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _64_59; FStar_Absyn_Syntax.lbdef = _64_57}) -> begin
(let _64_75 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_1 -> (match (_64_1) with
| FStar_Absyn_Syntax.Projector (_64_65) -> begin
true
end
| _64_68 -> begin
false
end)))) then begin
(let mname = (let _130_31 = (let _130_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _130_30))
in (FStar_All.pipe_right _130_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (let env = (let _130_33 = (let _130_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _130_32))
in (FStar_Extraction_ML_Env.extend_fv' env _130_33 mname ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit))
in (env, (let _64_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _64_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _64_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _64_71.FStar_Extraction_ML_Syntax.mllb_def}))))
end else begin
(let _130_35 = (let _130_34 = (FStar_Extraction_ML_Env.extend_lb env lbname t ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit)
in (FStar_All.pipe_left Prims.fst _130_34))
in (_130_35, ml_lb))
end
in (match (_64_75) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_64_78) with
| (g, ml_lbs') -> begin
(g, (FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
end))
end
| _64_80 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _130_37 = (let _130_36 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in (bs, _130_36))
in (FStar_Absyn_Syntax.mk_Exp_abs _130_37 None FStar_Absyn_Syntax.dummyRange))
end
| _64_92 -> begin
(fail_exp lid t)
end)
in (let se = FStar_Absyn_Syntax.Sig_let (((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _64_97 = (extract_sig g se)
in (match (_64_97) with
| (g, mlm) -> begin
(let is_record = (FStar_Util.for_some (fun _64_2 -> (match (_64_2) with
| FStar_Absyn_Syntax.RecordType (_64_100) -> begin
true
end
| _64_103 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _64_3 -> (match (_64_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _64_109 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _130_41 = (let _130_40 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_130_40)::[])
in (g, _130_41))
end
| _64_113 -> begin
(match ((FStar_Util.find_map quals (fun _64_4 -> (match (_64_4) with
| FStar_Absyn_Syntax.Projector (l, _64_117) -> begin
Some (l)
end
| _64_121 -> begin
None
end)))) with
| Some (_64_123) -> begin
(g, [])
end
| _64_126 -> begin
(g, mlm)
end)
end))
end))))
end else begin
(g, [])
end
end
| FStar_Absyn_Syntax.Sig_main (e, _64_129) -> begin
(let _64_137 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_64_137) with
| (ml_main, _64_134, _64_136) -> begin
(g, (FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

let extract_iface = (fun g m -> (let _130_47 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _130_47 Prims.fst)))

let rec extract = (fun g m -> (let _64_160 = (FStar_Absyn_Util.reset_gensym ())
in (let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (let g = (let _64_163 = g
in {FStar_Extraction_ML_Env.tcenv = _64_163.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _64_163.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _64_163.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (let _130_52 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str _130_52))) then begin
(let g = (extract_iface g m)
in (g, []))
end else begin
(let _64_169 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_64_169) with
| (g, sigs) -> begin
(let mlm = (FStar_List.flatten sigs)
in (let _130_57 = (let _130_56 = (let _130_55 = (let _130_54 = (let _130_53 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_130_53, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_130_54)::[])
in FStar_Extraction_ML_Syntax.MLLib (_130_55))
in (_130_56)::[])
in (g, _130_57)))
end))
end))))




