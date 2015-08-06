
let fail_exp = (fun ( lid ) ( t ) -> (let _70_25543 = (let _70_25542 = (Microsoft_FStar_Absyn_Util.fvar None Microsoft_FStar_Absyn_Const.failwith_lid Microsoft_FStar_Absyn_Syntax.dummyRange)
in (let _70_25541 = (let _70_25540 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_25539 = (let _70_25538 = (let _70_25537 = (let _70_25536 = (let _70_25535 = (let _70_25534 = (let _70_25533 = (let _70_25532 = (Microsoft_FStar_Absyn_Print.sli lid)
in (Support.String.strcat "Not yet implemented:" _70_25532))
in (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes _70_25533))
in (_70_25534, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_70_25535))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant _70_25536 None Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_25537))
in (_70_25538)::[])
in (_70_25540)::_70_25539))
in (_70_25542, _70_25541)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_25543 None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let rec extract_sig = (fun ( g ) ( se ) -> (let _62_9 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( u ) -> (let _70_25550 = (let _70_25549 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Microsoft.FStar.Util.format1 "now extracting :  %s \n" _70_25549))
in (Support.Microsoft.FStar.Util.print_string _70_25550))))
in (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_datacon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _62_25 = (Microsoft_FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_62_25) with
| (c, tds) -> begin
(c, tds)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, _62_29, _62_31)) -> begin
(let elet = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let (lbs, Microsoft_FStar_Absyn_Const.exp_false_bool) None r)
in (let _62_40 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_62_40) with
| (ml_let, _62_37, _62_39) -> begin
(match (ml_let) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let ((ml_lbs, _62_43)) -> begin
(let g = (Support.List.fold_left2 (fun ( env ) ( mllb ) ( _62_54 ) -> (match (_62_54) with
| {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _62_51; Microsoft_FStar_Absyn_Syntax.lbdef = _62_49} -> begin
(let _70_25555 = (let _70_25554 = (Support.Microsoft.FStar.Util.must mllb.Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc)
in (Microsoft_FStar_Extraction_ML_Env.extend_lb env lbname t _70_25554 mllb.Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit))
in (Support.All.pipe_left Support.Prims.fst _70_25555))
end)) g (Support.Prims.snd ml_lbs) (Support.Prims.snd lbs))
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Let (ml_lbs))::[]))
end
| _62_57 -> begin
(Support.All.failwith "impossible")
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r)) -> begin
(match ((Support.All.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption))) with
| true -> begin
(let impl = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((bs, c)) -> begin
(let _70_25557 = (let _70_25556 = (fail_exp lid (Microsoft_FStar_Absyn_Util.comp_result c))
in (bs, _70_25556))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_25557 None Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| _62_69 -> begin
(fail_exp lid t)
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_let (((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (lid); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ML_lid; Microsoft_FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _62_74 = (extract_sig g se)
in (match (_62_74) with
| (g, mlm) -> begin
(let is_record = (Support.Microsoft.FStar.Util.for_some (fun ( _62_1 ) -> (match (_62_1) with
| Microsoft_FStar_Absyn_Syntax.RecordType (_62_77) -> begin
true
end
| _62_80 -> begin
false
end)) quals)
in (match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _62_2 ) -> (match (_62_2) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _62_86 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _70_25561 = (let _70_25560 = (Microsoft_FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_70_25560)::[])
in (g, _70_25561))
end
| _62_90 -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _62_3 ) -> (match (_62_3) with
| Microsoft_FStar_Absyn_Syntax.Projector ((l, _62_94)) -> begin
Some (l)
end
| _62_98 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(g, [])
end
| _62_102 -> begin
(g, mlm)
end)
end))
end))))
end
| false -> begin
(g, [])
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _62_105)) -> begin
(let _62_113 = (Microsoft_FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_62_113) with
| (ml_main, _62_110, _62_112) -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_assume (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

let extract_iface = (fun ( g ) ( m ) -> (let _70_25567 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.All.pipe_right _70_25567 Support.Prims.fst)))

let rec extract = (fun ( g ) ( m ) -> (let name = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident m.Microsoft_FStar_Absyn_Syntax.name)
in (let _62_137 = (Support.Microsoft.FStar.Util.print_string (Support.String.strcat (Support.String.strcat "extracting: " m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str) "\n"))
in (let g = (let _62_139 = g
in {Microsoft_FStar_Extraction_ML_Env.tcenv = _62_139.Microsoft_FStar_Extraction_ML_Env.tcenv; Microsoft_FStar_Extraction_ML_Env.gamma = _62_139.Microsoft_FStar_Extraction_ML_Env.gamma; Microsoft_FStar_Extraction_ML_Env.tydefs = _62_139.Microsoft_FStar_Extraction_ML_Env.tydefs; Microsoft_FStar_Extraction_ML_Env.currentModule = name})
in (match (((m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str = "Prims") || m.Microsoft_FStar_Absyn_Syntax.is_interface)) with
| true -> begin
(let g = (extract_iface g m)
in (g, []))
end
| false -> begin
(let _62_145 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (match (_62_145) with
| (g, sigs) -> begin
(let mlm = (Support.List.flatten sigs)
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLLib ((((Microsoft_FStar_Extraction_ML_Util.flatten_mlpath name), Some (([], mlm)), Microsoft_FStar_Extraction_ML_Syntax.MLLib ([])))::[]))::[]))
end))
end)))))




