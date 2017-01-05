
open Prims

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_41_21); FStar_Syntax_Syntax.lbunivs = _41_19; FStar_Syntax_Syntax.lbtyp = _41_17; FStar_Syntax_Syntax.lbeff = _41_15; FStar_Syntax_Syntax.lbdef = _41_13})::[]), _41_27, _41_29, _41_31, _41_33) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (_41_37, _41_39, _41_41, _41_43, _41_45) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| _41_49 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
((FStar_Syntax_Syntax.Sig_bundle (((sigelts), (quals), (members), (rng)))), ([]))
end
| _41_53 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun _41_1 -> (match (_41_1) with
| FStar_Syntax_Syntax.Sig_let ((_41_56, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _41_64; FStar_Syntax_Syntax.lbtyp = _41_62; FStar_Syntax_Syntax.lbeff = _41_60; FStar_Syntax_Syntax.lbdef = _41_58})::[]), _41_71, _41_73, _41_75, _41_77) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _41_81 -> begin
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

let remove_not_unfolded = (fun lid -> (let _140_15 = (let _140_14 = (FStar_ST.read not_unfolded_yet)
in (FStar_All.pipe_right _140_14 (FStar_List.filter (fun _41_2 -> (match (_41_2) with
| FStar_Syntax_Syntax.Sig_let ((_41_90, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _41_98; FStar_Syntax_Syntax.lbtyp = _41_96; FStar_Syntax_Syntax.lbeff = _41_94; FStar_Syntax_Syntax.lbdef = _41_92})::[]), _41_105, _41_107, _41_109, _41_111) -> begin
(not ((FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| _41_115 -> begin
true
end)))))
in (FStar_ST.op_Colon_Equals not_unfolded_yet _140_15)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_41_123, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = _41_131; FStar_Syntax_Syntax.lbtyp = _41_129; FStar_Syntax_Syntax.lbeff = _41_127; FStar_Syntax_Syntax.lbdef = _41_125})::[]), _41_138, _41_140, _41_142, _41_144) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (x)
end
| _41_148 -> begin
None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_41_152, ({FStar_Syntax_Syntax.lbname = _41_161; FStar_Syntax_Syntax.lbunivs = _41_159; FStar_Syntax_Syntax.lbtyp = _41_157; FStar_Syntax_Syntax.lbeff = _41_155; FStar_Syntax_Syntax.lbdef = tm})::[]), _41_166, _41_168, _41_170, _41_172)) -> begin
Some (tm)
end
| _41_177 -> begin
None
end))
in (match ((let _140_25 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_Util.find_map _140_25 replacee_term))) with
| Some (x) -> begin
x
end
| None -> begin
(match ((FStar_Util.find_map type_abbrev_sigelts replacee)) with
| Some (se) -> begin
if (let _140_27 = (FStar_ST.read in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) _140_27)) then begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end else begin
(unfold_abbrev se)
end
end
| _41_186 -> begin
t
end)
end))))
and unfold_abbrev = (fun _41_4 -> (match (_41_4) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), rng, _41_194, quals, attr) -> begin
(

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun _41_3 -> (match (_41_3) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| _41_202 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _41_207 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in (

let _41_209 = (let _140_31 = (let _140_30 = (FStar_ST.read in_progress)
in (lid)::_140_30)
in (FStar_ST.op_Colon_Equals in_progress _140_31))
in (match (()) with
| () -> begin
(

let _41_210 = (remove_not_unfolded lid)
in (match (()) with
| () -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_abbrev_fv lb.FStar_Syntax_Syntax.lbtyp)
in (

let tm' = (FStar_Syntax_InstFV.inst unfold_abbrev_fv lb.FStar_Syntax_Syntax.lbdef)
in (

let lb' = (

let _41_213 = lb
in {FStar_Syntax_Syntax.lbname = _41_213.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _41_213.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = _41_213.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), (rng), ((lid)::[]), (quals), (attr)))
in (

let _41_217 = (let _140_33 = (let _140_32 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (sigelt')::_140_32)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs _140_33))
in (match (()) with
| () -> begin
(

let _41_218 = (let _140_35 = (let _140_34 = (FStar_ST.read in_progress)
in (FStar_List.tl _140_34))
in (FStar_ST.op_Colon_Equals in_progress _140_35))
in (match (()) with
| () -> begin
tm'
end))
end))))))
end))
end))))
end
| _41_220 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun _41_222 -> (match (()) with
| () -> begin
(match ((FStar_ST.read not_unfolded_yet)) with
| (x)::_41_224 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| _41_229 -> begin
(let _140_38 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_List.rev _140_38))
end)
end))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (not ((FStar_Ident.lid_equals lid lid')))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_41_239, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = _41_246; FStar_Syntax_Syntax.lbtyp = _41_244; FStar_Syntax_Syntax.lbeff = _41_242; FStar_Syntax_Syntax.lbdef = tm})::[]), _41_253, _41_255, _41_257, _41_259) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (tm)
end
| _41_263 -> begin
None
end))))
in (

let unfold_fv = (fun t fv -> (match ((find_in_unfolded fv)) with
| Some (t') -> begin
t'
end
| _41_270 -> begin
t
end))
in (

let unfold_in_sig = (fun _41_5 -> (match (_41_5) with
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
| FStar_Syntax_Syntax.Sig_let (_41_298, _41_300, _41_302, _41_304, _41_306) -> begin
[]
end
| _41_310 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (quals), (new_members), (rng)))
in ((new_bundle), (unfolded_type_abbrevs))))))))
end)))




