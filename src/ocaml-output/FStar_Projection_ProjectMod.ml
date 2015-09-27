
let rec project_sig = (fun m g se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
se
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, id, quals) -> begin
(let elet = (FStar_Absyn_Syntax.mk_Exp_let (lbs, FStar_Absyn_Const.exp_false_bool) None r)
in (let new_let = (FStar_Projection_ProjectExp.project_exp m g elet)
in (match (new_let.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
FStar_Absyn_Syntax.Sig_let ((lbs, r, id, quals))
end
| _67_29 -> begin
(FStar_All.failwith "Impossible!")
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
se
end
| FStar_Absyn_Syntax.Sig_main (e, _67_38) -> begin
se
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
se
end))

let project_iface = (fun g m -> (FStar_List.map (project_sig m g) m.FStar_Absyn_Syntax.declarations))

let rec project = (fun g m -> (match ((((m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (let _136_15 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str _136_15)))) with
| true -> begin
m
end
| false -> begin
(let sigs = (FStar_List.map (project_sig m g) m.FStar_Absyn_Syntax.declarations)
in (let new_mod = (let _67_64 = m
in {FStar_Absyn_Syntax.name = _67_64.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = sigs; FStar_Absyn_Syntax.exports = _67_64.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _67_64.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _67_64.FStar_Absyn_Syntax.is_deserialized})
in new_mod))
end))




