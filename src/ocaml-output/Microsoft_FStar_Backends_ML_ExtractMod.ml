
let fail_exp = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app ((Microsoft_FStar_Absyn_Util.fvar false Microsoft_FStar_Absyn_Const.failwith_lid Microsoft_FStar_Absyn_Syntax.dummyRange), ((Microsoft_FStar_Absyn_Syntax.varg (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant (Microsoft_FStar_Absyn_Syntax.Const_string (((Support.Microsoft.FStar.Bytes.string_as_unicode_bytes "Not yet implemented"), Microsoft_FStar_Absyn_Syntax.dummyRange))) None Microsoft_FStar_Absyn_Syntax.dummyRange)))::[]) None Microsoft_FStar_Absyn_Syntax.dummyRange)

let rec extract_sig = (fun ( g ) ( se ) -> (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_datacon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _55_18 = (Microsoft_FStar_Backends_ML_ExtractTyp.extractSigElt g se)
in (match (_55_18) with
| (c, tds) -> begin
(c, (Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (tds))::[])
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, _, _)) -> begin
(let elet = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let (lbs, Microsoft_FStar_Absyn_Const.exp_false_bool) None r)
in (let _55_33 = (Microsoft_FStar_Backends_ML_ExtractExp.synth_exp g elet)
in (match (_55_33) with
| (ml_let, _, _) -> begin
(match (ml_let) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let ((ml_lbs, _)) -> begin
(let g = (Support.List.fold_left2 (fun ( env ) ( _55_46 ) ( _55_53 ) -> (match ((_55_46, _55_53)) with
| ((id, poly_t, _, _), {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _}) -> begin
((Support.Prims.fst) (Microsoft_FStar_Backends_ML_Env.extend_lb env lbname t (Support.Microsoft.FStar.Util.must poly_t)))
end)) g (Support.Prims.snd ml_lbs) (Support.Prims.snd lbs))
in (g, (Microsoft_FStar_Backends_ML_Syntax.MLM_Let (ml_lbs))::[]))
end
| _ -> begin
(failwith "impossible")
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r)) -> begin
if ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption) quals) then begin
(let _55_66 = (Microsoft_FStar_Backends_ML_Util.tbinder_prefix t)
in (match (_55_66) with
| (tbinders, _) -> begin
(let impl = (match (tbinders) with
| [] -> begin
fail_exp
end
| bs -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, fail_exp) None Microsoft_FStar_Absyn_Syntax.dummyRange)
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_let (((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (lid); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_Tot_lid; Microsoft_FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _55_73 = (extract_sig g se)
in (match (_55_73) with
| (g, mlm) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun ( _55_1 ) -> (match (_55_1) with
| (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _ -> begin
false
end))) quals) then begin
(g, [])
end else begin
(g, mlm)
end
end))))
end))
end else begin
(g, [])
end
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _)) -> begin
(let _55_93 = (Microsoft_FStar_Backends_ML_ExtractExp.synth_exp g e)
in (match (_55_93) with
| (ml_main, _, _) -> begin
(g, (Microsoft_FStar_Backends_ML_Syntax.MLM_Top (ml_main))::[])
end))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_assume (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end))

let extract_prims = (fun ( g ) ( m ) -> ((Support.Prims.fst) (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)))

let rec extract = (fun ( g ) ( m ) -> (let name = (Microsoft_FStar_Backends_ML_Syntax.mlpath_of_lident m.Microsoft_FStar_Absyn_Syntax.name)
in (let g = (let _55_117 = g
in {Microsoft_FStar_Backends_ML_Env.tcenv = _55_117.Microsoft_FStar_Backends_ML_Env.tcenv; Microsoft_FStar_Backends_ML_Env.gamma = _55_117.Microsoft_FStar_Backends_ML_Env.gamma; Microsoft_FStar_Backends_ML_Env.tydefs = _55_117.Microsoft_FStar_Backends_ML_Env.tydefs; Microsoft_FStar_Backends_ML_Env.erasableTypes = _55_117.Microsoft_FStar_Backends_ML_Env.erasableTypes; Microsoft_FStar_Backends_ML_Env.currentModule = name})
in (let _55_120 = if m.Microsoft_FStar_Absyn_Syntax.is_interface then begin
(failwith "NYI")
end
in if (m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str = "Prims") then begin
(let g = (extract_prims g m)
in (g, Microsoft_FStar_Backends_ML_Syntax.MLLib ((("Prims", None, Microsoft_FStar_Backends_ML_Syntax.MLLib ([])))::[])))
end else begin
(let _55_125 = (Support.Microsoft.FStar.Util.fold_map extract_sig g m.Microsoft_FStar_Absyn_Syntax.declarations)
in (match (_55_125) with
| (g, sigs) -> begin
(let mlm = (Support.List.flatten sigs)
in (g, Microsoft_FStar_Backends_ML_Syntax.MLLib (((m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str, Some (([], mlm)), Microsoft_FStar_Backends_ML_Syntax.MLLib ([])))::[])))
end))
end))))




