
open Prims

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_42_21); FStar_Syntax_Syntax.lbunivs = _42_19; FStar_Syntax_Syntax.lbtyp = _42_17; FStar_Syntax_Syntax.lbeff = _42_15; FStar_Syntax_Syntax.lbdef = _42_13})::[]), _42_27, _42_29, _42_31, _42_33) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (_42_37, _42_39, _42_41, _42_43, _42_45) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| _42_49 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
((FStar_Syntax_Syntax.Sig_bundle (((sigelts), (quals), (members), (rng)))), ([]))
end
| _42_53 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun _42_1 -> (match (_42_1) with
| FStar_Syntax_Syntax.Sig_let ((_42_56, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _42_64; FStar_Syntax_Syntax.lbtyp = _42_62; FStar_Syntax_Syntax.lbeff = _42_60; FStar_Syntax_Syntax.lbdef = _42_58})::[]), _42_71, _42_73, _42_75, _42_77) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _42_81 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")
end))))
in (

let unfolded_type_abbrevs = (

let rev_unfolded_type_abbrevs = (FStar_Util.mk_ref [])
in (

let in_progress = (FStar_Util.mk_ref [])
in (

let not_unfolded_yet = (FStar_Util.mk_ref type_abbrev_sigelts)
in (

let remove_not_unfolded = (fun lid -> (let _143_15 = (let _143_14 = (FStar_ST.read not_unfolded_yet)
in (FStar_All.pipe_right _143_14 (FStar_List.filter (fun _42_2 -> (match (_42_2) with
| FStar_Syntax_Syntax.Sig_let ((_42_90, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _42_98; FStar_Syntax_Syntax.lbtyp = _42_96; FStar_Syntax_Syntax.lbeff = _42_94; FStar_Syntax_Syntax.lbdef = _42_92})::[]), _42_105, _42_107, _42_109, _42_111) -> begin
(not ((FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| _42_115 -> begin
true
end)))))
in (FStar_ST.op_Colon_Equals not_unfolded_yet _143_15)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_42_123, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = _42_131; FStar_Syntax_Syntax.lbtyp = _42_129; FStar_Syntax_Syntax.lbeff = _42_127; FStar_Syntax_Syntax.lbdef = _42_125})::[]), _42_138, _42_140, _42_142, _42_144) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (x)
end
| _42_148 -> begin
None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_42_152, ({FStar_Syntax_Syntax.lbname = _42_161; FStar_Syntax_Syntax.lbunivs = _42_159; FStar_Syntax_Syntax.lbtyp = _42_157; FStar_Syntax_Syntax.lbeff = _42_155; FStar_Syntax_Syntax.lbdef = tm})::[]), _42_166, _42_168, _42_170, _42_172)) -> begin
Some (tm)
end
| _42_177 -> begin
None
end))
in (match ((let _143_25 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_Util.find_map _143_25 replacee_term))) with
| Some (x) -> begin
x
end
| None -> begin
(match ((FStar_Util.find_map type_abbrev_sigelts replacee)) with
| Some (se) -> begin
if (let _143_27 = (FStar_ST.read in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) _143_27)) then begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end else begin
(unfold_abbrev se)
end
end
| _42_186 -> begin
t
end)
end))))
and unfold_abbrev = (fun _42_4 -> (match (_42_4) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), rng, _42_194, quals, attr) -> begin
(

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun _42_3 -> (match (_42_3) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| _42_202 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _42_207 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in (

let _42_209 = (let _143_31 = (let _143_30 = (FStar_ST.read in_progress)
in (lid)::_143_30)
in (FStar_ST.op_Colon_Equals in_progress _143_31))
in (match (()) with
| () -> begin
(

let _42_210 = (remove_not_unfolded lid)
in (match (()) with
| () -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_abbrev_fv lb.FStar_Syntax_Syntax.lbtyp)
in (

let tm' = (FStar_Syntax_InstFV.inst unfold_abbrev_fv lb.FStar_Syntax_Syntax.lbdef)
in (

let lb' = (

let _42_213 = lb
in {FStar_Syntax_Syntax.lbname = _42_213.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _42_213.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = _42_213.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), (rng), ((lid)::[]), (quals), (attr)))
in (

let _42_217 = (let _143_33 = (let _143_32 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (sigelt')::_143_32)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs _143_33))
in (match (()) with
| () -> begin
(

let _42_218 = (let _143_35 = (let _143_34 = (FStar_ST.read in_progress)
in (FStar_List.tl _143_34))
in (FStar_ST.op_Colon_Equals in_progress _143_35))
in (match (()) with
| () -> begin
tm'
end))
end))))))
end))
end))))
end
| _42_220 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun _42_222 -> (match (()) with
| () -> begin
(match ((FStar_ST.read not_unfolded_yet)) with
| (x)::_42_224 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| _42_229 -> begin
(let _143_38 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_List.rev _143_38))
end)
end))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (not ((FStar_Ident.lid_equals lid lid')))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_42_239, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = _42_246; FStar_Syntax_Syntax.lbtyp = _42_244; FStar_Syntax_Syntax.lbeff = _42_242; FStar_Syntax_Syntax.lbdef = tm})::[]), _42_253, _42_255, _42_257, _42_259) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (tm)
end
| _42_263 -> begin
None
end))))
in (

let unfold_fv = (fun t fv -> (match ((find_in_unfolded fv)) with
| Some (t') -> begin
t'
end
| _42_270 -> begin
t
end))
in (

let unfold_in_sig = (fun _42_5 -> (match (_42_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, bnd, ty, mut, dc, quals, rng) -> begin
(

let bnd' = (FStar_Syntax_InstFV.inst_binders unfold_fv bnd)
in (

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in (FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs), (bnd'), (ty'), (mut'), (dc), (quals), (rng))))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, ty, res, npars, quals, mut, rng) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in (FStar_Syntax_Syntax.Sig_datacon (((lid), (univs), (ty'), (res), (npars), (quals), (mut'), (rng))))::[]))
end
| FStar_Syntax_Syntax.Sig_let (_42_298, _42_300, _42_302, _42_304, _42_306) -> begin
[]
end
| _42_310 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (quals), (new_members), (rng)))
in ((new_bundle), (unfolded_type_abbrevs))))))))
end)))




