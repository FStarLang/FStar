
let fail_exp = (fun ( t ) -> (let _68_25326 = (let _68_25325 = (Microsoft_FStar_Absyn_Util.fvar None Microsoft_FStar_Absyn_Const.failwith_lid Microsoft_FStar_Absyn_Syntax.dummyRange)
in (let _68_25324 = (let _68_25323 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_25322 = (let _68_25321 = (let _68_25320 = (let _68_25319 = (let _68_25318 = (let _68_25317 = (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes "Not yet implemented")
in (_68_25317, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_68_25318))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant _68_25319 None Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _68_25320))
in (_68_25321)::[])
in (_68_25323)::_68_25322))
in (_68_25325, _68_25324)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_25326 None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let rec extract_sig = (fun ( g ) ( se ) -> (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_datacon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _60_21 = (Microsoft_FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_60_21) with
| (c, tds) -> begin
(c, tds)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, _, _)) -> begin
(let elet = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let (lbs, Microsoft_FStar_Absyn_Const.exp_false_bool) None r)
in (let _60_36 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_60_36) with
| (ml_let, _, _) -> begin
(match (ml_let) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let ((ml_lbs, _)) -> begin
(let g = (Support.List.fold_left2 (fun ( env ) ( mllb ) ( _60_50 ) -> (match (_60_50) with
| {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _} -> begin
(let _68_25335 = (let _68_25334 = (Support.Microsoft.FStar.Util.must mllb.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc)
in (Microsoft_FStar_Extraction_ML_Env.extend_lb env lbname t _68_25334 mllb.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit))
in (Support.Prims.pipe_left Support.Prims.fst _68_25335))
end)) g (Support.Prims.snd ml_lbs) (Support.Prims.snd lbs))
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Let (ml_lbs))::[]))
end
| _ -> begin
(failwith ("impossible"))
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r)) -> begin
(match ((Support.Prims.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption))) with
| true -> begin
(let impl = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((bs, c)) -> begin
(let _68_25337 = (let _68_25336 = (fail_exp (Microsoft_FStar_Absyn_Util.comp_result c))
in (bs, _68_25336))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _68_25337 None Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| _ -> begin
(fail_exp t)
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_let (((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (lid); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ML_lid; Microsoft_FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _60_70 = (extract_sig g se)
in (match (_60_70) with
| (g, mlm) -> begin
(let is_record = (Support.Microsoft.FStar.Util.for_some (fun ( _60_1 ) -> (match (_60_1) with
| Microsoft_FStar_Absyn_Syntax.RecordType (_) -> begin
true
end
| _ -> begin
false
end)) quals)
in (match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _60_2 ) -> (match (_60_2) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _ -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _68_25341 = (let _68_25340 = (Microsoft_FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_68_25340)::[])
in (g, _68_25341))
end
| _ -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _60_3 ) -> (match (_60_3) with
| Microsoft_FStar_Absyn_Syntax.Projector ((l, _)) -> begin
Some (l)
end
| _ -> begin
None
end)))) with
| Some (l) -> begin
(g, [])
end
| None -> begin
(g, mlm)
end)
end))
end))))
end
| false -> begin
(g, [])
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _)) -> begin
(let _60_108 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_60_108) with
| (ml_main, _, _) -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_assume (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end))

let extract_iface = (fun ( g ) ( m ) -> (let _68_25347 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.Prims.pipe_right _68_25347 Support.Prims.fst)))

let rec extract = (fun ( g ) ( m ) -> (let name = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident m.Microsoft_FStar_Absyn_Syntax.name)
in (let _60_132 = (Support.Microsoft.FStar.Util.print_string (Support.String.strcat (Support.String.strcat "extracting: " m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str) "\n"))
in (let g = (let _60_134 = g
in {Microsoft_FStar_Extraction_ML_Env.tcenv = _60_134.Microsoft_FStar_Extraction_ML_Env.tcenv; Microsoft_FStar_Extraction_ML_Env.gamma = _60_134.Microsoft_FStar_Extraction_ML_Env.gamma; Microsoft_FStar_Extraction_ML_Env.tydefs = _60_134.Microsoft_FStar_Extraction_ML_Env.tydefs; Microsoft_FStar_Extraction_ML_Env.erasableTypes = _60_134.Microsoft_FStar_Extraction_ML_Env.erasableTypes; Microsoft_FStar_Extraction_ML_Env.currentModule = name})
in (match (((m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str = "Prims") || m.Microsoft_FStar_Absyn_Syntax.is_interface)) with
| true -> begin
(let g = (extract_iface g m)
in (g, []))
end
| false -> begin
(let _60_140 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (match (_60_140) with
| (g, sigs) -> begin
(let mlm = (Support.List.flatten sigs)
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLLib ((((Microsoft_FStar_Extraction_ML_Util.flatten_mlpath name), Some (([], mlm)), Microsoft_FStar_Extraction_ML_Syntax.MLLib ([])))::[]))::[]))
end))
end)))))




