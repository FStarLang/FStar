
let fail_exp = (fun ( lid ) ( t ) -> (let _126_16 = (let _126_15 = (Microsoft_FStar_Absyn_Util.fvar None Microsoft_FStar_Absyn_Const.failwith_lid Microsoft_FStar_Absyn_Syntax.dummyRange)
in (let _126_14 = (let _126_13 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _126_12 = (let _126_11 = (let _126_10 = (let _126_9 = (let _126_8 = (let _126_7 = (let _126_6 = (let _126_5 = (Microsoft_FStar_Absyn_Print.sli lid)
in (Support.String.strcat "Not yet implemented:" _126_5))
in (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes _126_6))
in (_126_7, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_126_8))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant _126_9 None Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _126_10))
in (_126_11)::[])
in (_126_13)::_126_12))
in (_126_15, _126_14)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _126_16 None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let mangle_projector_lid = (fun ( x ) -> (let projecteeName = x.Microsoft_FStar_Absyn_Syntax.ident
in (let _62_11 = (Support.Microsoft.FStar.Util.prefix x.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_62_11) with
| (prefix, constrName) -> begin
(let mangledName = (Microsoft_FStar_Absyn_Syntax.id_of_text (Support.String.strcat (Support.String.strcat (Support.String.strcat "___" constrName.Microsoft_FStar_Absyn_Syntax.idText) "___") projecteeName.Microsoft_FStar_Absyn_Syntax.idText))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append prefix ((mangledName)::[]))))
end))))

let rec extract_sig = (fun ( g ) ( se ) -> (let _62_16 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( u ) -> (let _126_25 = (let _126_24 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Microsoft.FStar.Util.format1 "now extracting :  %s \n" _126_24))
in (Support.Microsoft.FStar.Util.print_string _126_25))))
in (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_datacon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _62_32 = (Microsoft_FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_62_32) with
| (c, tds) -> begin
(c, tds)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, _62_36, quals)) -> begin
(let elet = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let (lbs, Microsoft_FStar_Absyn_Const.exp_false_bool) None r)
in (let _62_46 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_62_46) with
| (ml_let, _62_43, _62_45) -> begin
(match (ml_let) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let ((ml_lbs, _62_49)) -> begin
(let _62_78 = (Support.List.fold_left2 (fun ( _62_54 ) ( ml_lb ) ( _62_62 ) -> (match ((_62_54, _62_62)) with
| ((env, ml_lbs), {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _62_59; Microsoft_FStar_Absyn_Syntax.lbdef = _62_57}) -> begin
(let _62_75 = (match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _62_1 ) -> (match (_62_1) with
| Microsoft_FStar_Absyn_Syntax.Projector (_62_65) -> begin
true
end
| _62_68 -> begin
false
end))))) with
| true -> begin
(let mname = (let _126_31 = (let _126_30 = (Support.Microsoft.FStar.Util.right lbname)
in (mangle_projector_lid _126_30))
in (Support.All.pipe_right _126_31 Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (let env = (let _126_34 = (let _126_32 = (Support.Microsoft.FStar.Util.right lbname)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.fv _126_32))
in (let _126_33 = (Support.Microsoft.FStar.Util.must ml_lb.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc)
in (Microsoft_FStar_Extraction_ML_Env.extend_fv' env _126_34 mname _126_33 ml_lb.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit)))
in (env, (let _62_71 = ml_lb
in {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = ((Support.Prims.snd mname), 0); Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = _62_71.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = _62_71.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = _62_71.Microsoft_FStar_Extraction_ML_Syntax.mllb_def}))))
end
| false -> begin
(let _126_37 = (let _126_36 = (let _126_35 = (Support.Microsoft.FStar.Util.must ml_lb.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc)
in (Microsoft_FStar_Extraction_ML_Env.extend_lb env lbname t _126_35 ml_lb.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit))
in (Support.All.pipe_left Support.Prims.fst _126_36))
in (_126_37, ml_lb))
end)
in (match (_62_75) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end))
end)) (g, []) (Support.Prims.snd ml_lbs) (Support.Prims.snd lbs))
in (match (_62_78) with
| (g, ml_lbs') -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Let (((Support.Prims.fst ml_lbs), (Support.List.rev ml_lbs'))))::[])
end))
end
| _62_80 -> begin
(Support.All.failwith "impossible")
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r)) -> begin
(match ((Support.All.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption))) with
| true -> begin
(let impl = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((bs, c)) -> begin
(let _126_39 = (let _126_38 = (fail_exp lid (Microsoft_FStar_Absyn_Util.comp_result c))
in (bs, _126_38))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _126_39 None Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| _62_92 -> begin
(fail_exp lid t)
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_let (((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (lid); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ML_lid; Microsoft_FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _62_97 = (extract_sig g se)
in (match (_62_97) with
| (g, mlm) -> begin
(let is_record = (Support.Microsoft.FStar.Util.for_some (fun ( _62_2 ) -> (match (_62_2) with
| Microsoft_FStar_Absyn_Syntax.RecordType (_62_100) -> begin
true
end
| _62_103 -> begin
false
end)) quals)
in (match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _62_3 ) -> (match (_62_3) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _62_109 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _126_43 = (let _126_42 = (Microsoft_FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_126_42)::[])
in (g, _126_43))
end
| _62_113 -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _62_4 ) -> (match (_62_4) with
| Microsoft_FStar_Absyn_Syntax.Projector ((l, _62_117)) -> begin
Some (l)
end
| _62_121 -> begin
None
end)))) with
| Some (_62_123) -> begin
(g, [])
end
| _62_126 -> begin
(g, mlm)
end)
end))
end))))
end
| false -> begin
(g, [])
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _62_129)) -> begin
(let _62_137 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_62_137) with
| (ml_main, _62_134, _62_136) -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_assume (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

let extract_iface = (fun ( g ) ( m ) -> (let _126_49 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.All.pipe_right _126_49 Support.Prims.fst)))

let rec extract = (fun ( g ) ( m ) -> (let _62_160 = (Microsoft_FStar_Absyn_Util.reset_gensym ())
in (let name = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident m.Microsoft_FStar_Absyn_Syntax.name)
in (let _62_163 = (Support.Microsoft.FStar.Util.print_string (Support.String.strcat (Support.String.strcat "extracting: " m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str) "\n"))
in (let g = (let _62_165 = g
in {Microsoft_FStar_Extraction_ML_Env.tcenv = _62_165.Microsoft_FStar_Extraction_ML_Env.tcenv; Microsoft_FStar_Extraction_ML_Env.gamma = _62_165.Microsoft_FStar_Extraction_ML_Env.gamma; Microsoft_FStar_Extraction_ML_Env.tydefs = _62_165.Microsoft_FStar_Extraction_ML_Env.tydefs; Microsoft_FStar_Extraction_ML_Env.currentModule = name})
in (match (((m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str = "Prims") || m.Microsoft_FStar_Absyn_Syntax.is_interface)) with
| true -> begin
(let g = (extract_iface g m)
in (g, []))
end
| false -> begin
(let _62_171 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (match (_62_171) with
| (g, sigs) -> begin
(let mlm = (Support.List.flatten sigs)
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLLib ((((Microsoft_FStar_Extraction_ML_Util.flatten_mlpath name), Some (([], mlm)), Microsoft_FStar_Extraction_ML_Syntax.MLLib ([])))::[]))::[]))
end))
end))))))




