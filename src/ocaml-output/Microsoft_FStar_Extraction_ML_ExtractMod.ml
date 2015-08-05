
let fail_exp = (fun ( lid ) ( t ) -> (let _68_25421 = (let _68_25420 = (Microsoft_FStar_Absyn_Util.fvar None Microsoft_FStar_Absyn_Const.failwith_lid Microsoft_FStar_Absyn_Syntax.dummyRange)
in (let _68_25419 = (let _68_25418 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_25417 = (let _68_25416 = (let _68_25415 = (let _68_25414 = (let _68_25413 = (let _68_25412 = (let _68_25411 = (let _68_25410 = (Microsoft_FStar_Absyn_Print.sli lid)
in (Support.String.strcat "Not yet implemented:" _68_25410))
in (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes _68_25411))
in (_68_25412, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_68_25413))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant _68_25414 None Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _68_25415))
in (_68_25416)::[])
in (_68_25418)::_68_25417))
in (_68_25420, _68_25419)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_25421 None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let rec extract_sig = (fun ( g ) ( se ) -> (let _60_9 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( u ) -> (let _68_25428 = (let _68_25427 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Microsoft.FStar.Util.format1 "now extracting :  %s \n" _68_25427))
in (Support.Microsoft.FStar.Util.print_string _68_25428))))
in (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_datacon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _60_25 = (Microsoft_FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_60_25) with
| (c, tds) -> begin
(c, tds)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, _60_29, _60_31)) -> begin
(let elet = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let (lbs, Microsoft_FStar_Absyn_Const.exp_false_bool) None r)
in (let _60_40 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_60_40) with
| (ml_let, _60_37, _60_39) -> begin
(match (ml_let) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let ((ml_lbs, _60_43)) -> begin
(let g = (Support.List.fold_left2 (fun ( env ) ( mllb ) ( _60_54 ) -> (match (_60_54) with
| {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _60_51; Microsoft_FStar_Absyn_Syntax.lbdef = _60_49} -> begin
(let _68_25433 = (let _68_25432 = (Support.Microsoft.FStar.Util.must mllb.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc)
in (Microsoft_FStar_Extraction_ML_Env.extend_lb env lbname t _68_25432 mllb.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit))
in (Support.Prims.pipe_left Support.Prims.fst _68_25433))
end)) g (Support.Prims.snd ml_lbs) (Support.Prims.snd lbs))
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Let (ml_lbs))::[]))
end
| _60_57 -> begin
(failwith ("impossible"))
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r)) -> begin
(match ((Support.Prims.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption))) with
| true -> begin
(let impl = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((bs, c)) -> begin
(let _68_25435 = (let _68_25434 = (fail_exp lid (Microsoft_FStar_Absyn_Util.comp_result c))
in (bs, _68_25434))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _68_25435 None Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| _60_69 -> begin
(fail_exp lid t)
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_let (((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (lid); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ML_lid; Microsoft_FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _60_74 = (extract_sig g se)
in (match (_60_74) with
| (g, mlm) -> begin
(let is_record = (Support.Microsoft.FStar.Util.for_some (fun ( _60_1 ) -> (match (_60_1) with
| Microsoft_FStar_Absyn_Syntax.RecordType (_60_77) -> begin
true
end
| _60_80 -> begin
false
end)) quals)
in (match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _60_2 ) -> (match (_60_2) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _60_86 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _68_25439 = (let _68_25438 = (Microsoft_FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_68_25438)::[])
in (g, _68_25439))
end
| _60_90 -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _60_3 ) -> (match (_60_3) with
| Microsoft_FStar_Absyn_Syntax.Projector ((l, _60_94)) -> begin
Some (l)
end
| _60_98 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(g, [])
end
| _60_102 -> begin
(g, mlm)
end)
end))
end))))
end
| false -> begin
(g, [])
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _60_105)) -> begin
(let _60_113 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_60_113) with
| (ml_main, _60_110, _60_112) -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_assume (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

let extract_iface = (fun ( g ) ( m ) -> (let _68_25445 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.Prims.pipe_right _68_25445 Support.Prims.fst)))

let rec extract = (fun ( g ) ( m ) -> (let name = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident m.Microsoft_FStar_Absyn_Syntax.name)
in (let _60_137 = (Support.Microsoft.FStar.Util.print_string (Support.String.strcat (Support.String.strcat "extracting: " m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str) "\n"))
in (let g = (let _60_139 = g
in {Microsoft_FStar_Extraction_ML_Env.tcenv = _60_139.Microsoft_FStar_Extraction_ML_Env.tcenv; Microsoft_FStar_Extraction_ML_Env.gamma = _60_139.Microsoft_FStar_Extraction_ML_Env.gamma; Microsoft_FStar_Extraction_ML_Env.tydefs = _60_139.Microsoft_FStar_Extraction_ML_Env.tydefs; Microsoft_FStar_Extraction_ML_Env.currentModule = name})
in (match (((m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str = "Prims") || m.Microsoft_FStar_Absyn_Syntax.is_interface)) with
| true -> begin
(let g = (extract_iface g m)
in (g, []))
end
| false -> begin
(let _60_145 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (match (_60_145) with
| (g, sigs) -> begin
(let mlm = (Support.List.flatten sigs)
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLLib ((((Microsoft_FStar_Extraction_ML_Util.flatten_mlpath name), Some (([], mlm)), Microsoft_FStar_Extraction_ML_Syntax.MLLib ([])))::[]))::[]))
end))
end)))))




