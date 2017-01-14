
open Prims

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_42_16); FStar_Syntax_Syntax.lbunivs = _42_14; FStar_Syntax_Syntax.lbtyp = _42_12; FStar_Syntax_Syntax.lbeff = _42_10; FStar_Syntax_Syntax.lbdef = _42_8})::[]), _42_22, _42_24, _42_26, _42_28) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (_42_32, _42_34, _42_36, _42_38, _42_40) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| _42_44 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
((FStar_Syntax_Syntax.Sig_bundle (((sigelts), (quals), (members), (rng)))), ([]))
end
| _42_48 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun uu___97 -> (match (uu___97) with
| FStar_Syntax_Syntax.Sig_let ((_42_51, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _42_59; FStar_Syntax_Syntax.lbtyp = _42_57; FStar_Syntax_Syntax.lbeff = _42_55; FStar_Syntax_Syntax.lbdef = _42_53})::[]), _42_66, _42_68, _42_70, _42_72) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _42_76 -> begin
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
in (FStar_All.pipe_right _143_14 (FStar_List.filter (fun uu___98 -> (match (uu___98) with
| FStar_Syntax_Syntax.Sig_let ((_42_85, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _42_93; FStar_Syntax_Syntax.lbtyp = _42_91; FStar_Syntax_Syntax.lbeff = _42_89; FStar_Syntax_Syntax.lbdef = _42_87})::[]), _42_100, _42_102, _42_104, _42_106) -> begin
(not ((FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| _42_110 -> begin
true
end)))))
in (FStar_ST.op_Colon_Equals not_unfolded_yet _143_15)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_42_118, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = _42_126; FStar_Syntax_Syntax.lbtyp = _42_124; FStar_Syntax_Syntax.lbeff = _42_122; FStar_Syntax_Syntax.lbdef = _42_120})::[]), _42_133, _42_135, _42_137, _42_139) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (x)
end
| _42_143 -> begin
None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_42_147, ({FStar_Syntax_Syntax.lbname = _42_156; FStar_Syntax_Syntax.lbunivs = _42_154; FStar_Syntax_Syntax.lbtyp = _42_152; FStar_Syntax_Syntax.lbeff = _42_150; FStar_Syntax_Syntax.lbdef = tm})::[]), _42_161, _42_163, _42_165, _42_167)) -> begin
Some (tm)
end
| _42_172 -> begin
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
| _42_181 -> begin
t
end)
end))))
and unfold_abbrev = (fun uu___100 -> (match (uu___100) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), rng, _42_189, quals, attr) -> begin
(

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___99 -> (match (uu___99) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| _42_197 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _42_202 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in (

let _42_204 = (let _143_31 = (let _143_30 = (FStar_ST.read in_progress)
in (lid)::_143_30)
in (FStar_ST.op_Colon_Equals in_progress _143_31))
in (match (()) with
| () -> begin
(

let _42_205 = (remove_not_unfolded lid)
in (match (()) with
| () -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_abbrev_fv lb.FStar_Syntax_Syntax.lbtyp)
in (

let tm' = (FStar_Syntax_InstFV.inst unfold_abbrev_fv lb.FStar_Syntax_Syntax.lbdef)
in (

let lb' = (

let _42_208 = lb
in {FStar_Syntax_Syntax.lbname = _42_208.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _42_208.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = _42_208.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), (rng), ((lid)::[]), (quals), (attr)))
in (

let _42_212 = (let _143_33 = (let _143_32 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (sigelt')::_143_32)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs _143_33))
in (match (()) with
| () -> begin
(

let _42_213 = (let _143_35 = (let _143_34 = (FStar_ST.read in_progress)
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
| _42_215 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun _42_217 -> (match (()) with
| () -> begin
(match ((FStar_ST.read not_unfolded_yet)) with
| (x)::_42_219 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| _42_224 -> begin
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
| FStar_Syntax_Syntax.Sig_let ((_42_234, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = _42_241; FStar_Syntax_Syntax.lbtyp = _42_239; FStar_Syntax_Syntax.lbeff = _42_237; FStar_Syntax_Syntax.lbdef = tm})::[]), _42_248, _42_250, _42_252, _42_254) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (tm)
end
| _42_258 -> begin
None
end))))
in (

let unfold_fv = (fun t fv -> (match ((find_in_unfolded fv)) with
| Some (t') -> begin
t'
end
| _42_265 -> begin
t
end))
in (

let unfold_in_sig = (fun uu___101 -> (match (uu___101) with
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
| FStar_Syntax_Syntax.Sig_let (_42_293, _42_295, _42_297, _42_299, _42_301) -> begin
[]
end
| _42_305 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (quals), (new_members), (rng)))
in ((new_bundle), (unfolded_type_abbrevs))))))))
end)))




