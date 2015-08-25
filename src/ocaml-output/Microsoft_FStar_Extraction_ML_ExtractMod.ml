
let fail_exp = (fun lid t -> (let _130_16 = (let _130_15 = (Microsoft_FStar_Absyn_Util.fvar None Microsoft_FStar_Absyn_Const.failwith_lid Microsoft_FStar_Absyn_Syntax.dummyRange)
in (let _130_14 = (let _130_13 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _130_12 = (let _130_11 = (let _130_10 = (let _130_9 = (let _130_8 = (let _130_7 = (let _130_6 = (let _130_5 = (Microsoft_FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _130_5))
in (Microsoft_FStar_Bytes.string_as_unicode_bytes _130_6))
in (_130_7, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_130_8))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant _130_9 None Microsoft_FStar_Absyn_Syntax.dummyRange))
in (All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _130_10))
in (_130_11)::[])
in (_130_13)::_130_12))
in (_130_15, _130_14)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _130_16 None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let mangle_projector_lid = (fun x -> (let projecteeName = x.Microsoft_FStar_Absyn_Syntax.ident
in (let _64_11 = (Microsoft_FStar_Util.prefix x.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_64_11) with
| (prefix, constrName) -> begin
(let mangledName = (Microsoft_FStar_Absyn_Syntax.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.Microsoft_FStar_Absyn_Syntax.idText) "___") projecteeName.Microsoft_FStar_Absyn_Syntax.idText))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Microsoft_FStar_List.append prefix ((mangledName)::[]))))
end))))

let rec extract_sig = (fun g se -> (let _64_16 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun u -> (let _130_25 = (let _130_24 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Microsoft_FStar_Util.format1 "now extracting :  %s \n" _130_24))
in (Microsoft_FStar_Util.print_string _130_25))))
in (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_datacon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _64_32 = (Microsoft_FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_64_32) with
| (c, tds) -> begin
(c, tds)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (lbs, r, _64_36, quals) -> begin
(let elet = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let (lbs, Microsoft_FStar_Absyn_Const.exp_false_bool) None r)
in (let _64_46 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_64_46) with
| (ml_let, _64_43, _64_45) -> begin
(match (ml_let) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _64_49) -> begin
(let _64_78 = (Microsoft_FStar_List.fold_left2 (fun _64_54 ml_lb _64_62 -> (match ((_64_54, _64_62)) with
| ((env, ml_lbs), {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _64_59; Microsoft_FStar_Absyn_Syntax.lbdef = _64_57}) -> begin
(let _64_75 = (match ((All.pipe_right quals (Microsoft_FStar_Util.for_some (fun _64_1 -> (match (_64_1) with
| Microsoft_FStar_Absyn_Syntax.Projector (_64_65) -> begin
true
end
| _64_68 -> begin
false
end))))) with
| true -> begin
(let mname = (let _130_31 = (let _130_30 = (Microsoft_FStar_Util.right lbname)
in (mangle_projector_lid _130_30))
in (All.pipe_right _130_31 Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (let env = (let _130_34 = (let _130_32 = (Microsoft_FStar_Util.right lbname)
in (All.pipe_left Microsoft_FStar_Absyn_Util.fv _130_32))
in (let _130_33 = (Microsoft_FStar_Util.must ml_lb.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc)
in (Microsoft_FStar_Extraction_ML_Env.extend_fv' env _130_34 mname _130_33 ml_lb.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit)))
in (env, (let _64_71 = ml_lb
in {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = _64_71.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = _64_71.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = _64_71.Microsoft_FStar_Extraction_ML_Syntax.mllb_def}))))
end
| false -> begin
(let _130_37 = (let _130_36 = (let _130_35 = (Microsoft_FStar_Util.must ml_lb.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc)
in (Microsoft_FStar_Extraction_ML_Env.extend_lb env lbname t _130_35 ml_lb.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit))
in (All.pipe_left Prims.fst _130_36))
in (_130_37, ml_lb))
end)
in (match (_64_75) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_64_78) with
| (g, ml_lbs') -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (Microsoft_FStar_List.rev ml_lbs'))))::[])
end))
end
| _64_80 -> begin
(All.failwith "impossible")
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(match ((All.pipe_right quals (Microsoft_FStar_List.contains Microsoft_FStar_Absyn_Syntax.Assumption))) with
| true -> begin
(let impl = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _130_39 = (let _130_38 = (fail_exp lid (Microsoft_FStar_Absyn_Util.comp_result c))
in (bs, _130_38))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _130_39 None Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| _64_92 -> begin
(fail_exp lid t)
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_let (((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Microsoft_FStar_Util.Inr (lid); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ML_lid; Microsoft_FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _64_97 = (extract_sig g se)
in (match (_64_97) with
| (g, mlm) -> begin
(let is_record = (Microsoft_FStar_Util.for_some (fun _64_2 -> (match (_64_2) with
| Microsoft_FStar_Absyn_Syntax.RecordType (_64_100) -> begin
true
end
| _64_103 -> begin
false
end)) quals)
in (match ((Microsoft_FStar_Util.find_map quals (fun _64_3 -> (match (_64_3) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _64_109 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _130_43 = (let _130_42 = (Microsoft_FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_130_42)::[])
in (g, _130_43))
end
| _64_113 -> begin
(match ((Microsoft_FStar_Util.find_map quals (fun _64_4 -> (match (_64_4) with
| Microsoft_FStar_Absyn_Syntax.Projector (l, _64_117) -> begin
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
end
| false -> begin
(g, [])
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main (e, _64_129) -> begin
(let _64_137 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_64_137) with
| (ml_main, _64_134, _64_136) -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_assume (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

let extract_iface = (fun g m -> (let _130_49 = (Microsoft_FStar_Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (All.pipe_right _130_49 Prims.fst)))

let rec extract = (fun g m -> (let _64_160 = (Microsoft_FStar_Absyn_Util.reset_gensym ())
in (let name = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident m.Microsoft_FStar_Absyn_Syntax.name)
in (let _64_163 = (Microsoft_FStar_Util.print_string (Prims.strcat (Prims.strcat "extracting: " m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str) "\n"))
in (let g = (let _64_165 = g
in {Microsoft_FStar_Extraction_ML_Env.tcenv = _64_165.Microsoft_FStar_Extraction_ML_Env.tcenv; Microsoft_FStar_Extraction_ML_Env.gamma = _64_165.Microsoft_FStar_Extraction_ML_Env.gamma; Microsoft_FStar_Extraction_ML_Env.tydefs = _64_165.Microsoft_FStar_Extraction_ML_Env.tydefs; Microsoft_FStar_Extraction_ML_Env.currentModule = name})
in (match (((m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str = "Prims") || m.Microsoft_FStar_Absyn_Syntax.is_interface)) with
| true -> begin
(let g = (extract_iface g m)
in (g, []))
end
| false -> begin
(let _64_171 = (Microsoft_FStar_Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (match (_64_171) with
| (g, sigs) -> begin
(let mlm = (Microsoft_FStar_List.flatten sigs)
in (let _130_58 = (let _130_57 = (let _130_56 = (let _130_55 = (let _130_54 = (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath name)
in (_130_54, Some (([], mlm)), Microsoft_FStar_Extraction_ML_Syntax.MLLib ([])))
in (_130_55)::[])
in Microsoft_FStar_Extraction_ML_Syntax.MLLib (_130_56))
in (_130_57)::[])
in (g, _130_58)))
end))
end))))))




