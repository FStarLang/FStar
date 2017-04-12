
open Prims

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____31); FStar_Syntax_Syntax.lbunivs = uu____32; FStar_Syntax_Syntax.lbtyp = uu____33; FStar_Syntax_Syntax.lbeff = uu____34; FStar_Syntax_Syntax.lbdef = uu____35})::[]), uu____36, uu____37, uu____38) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____54, uu____55, uu____56, uu____57) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____65 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (quals), (members))); FStar_Syntax_Syntax.sigrng = rng}), ([]))
end
| uu____73 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____80, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____82; FStar_Syntax_Syntax.lbtyp = uu____83; FStar_Syntax_Syntax.lbeff = uu____84; FStar_Syntax_Syntax.lbdef = uu____85})::[]), uu____86, uu____87, uu____88) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____108 -> begin
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

let remove_not_unfolded = (fun lid -> (

let uu____130 = (

let uu____132 = (FStar_ST.read not_unfolded_yet)
in (FStar_All.pipe_right uu____132 (FStar_List.filter (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____140, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____142; FStar_Syntax_Syntax.lbtyp = uu____143; FStar_Syntax_Syntax.lbeff = uu____144; FStar_Syntax_Syntax.lbdef = uu____145})::[]), uu____146, uu____147, uu____148) -> begin
(not ((FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| uu____168 -> begin
true
end)))))
in (FStar_ST.write not_unfolded_yet uu____130)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____188, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____190; FStar_Syntax_Syntax.lbtyp = uu____191; FStar_Syntax_Syntax.lbeff = uu____192; FStar_Syntax_Syntax.lbdef = uu____193})::[]), uu____194, uu____195, uu____196) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (x)
end
| uu____220 -> begin
None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____231, ({FStar_Syntax_Syntax.lbname = uu____232; FStar_Syntax_Syntax.lbunivs = uu____233; FStar_Syntax_Syntax.lbtyp = uu____234; FStar_Syntax_Syntax.lbeff = uu____235; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____237, uu____238, uu____239); FStar_Syntax_Syntax.sigrng = uu____240}) -> begin
Some (tm)
end
| uu____260 -> begin
None
end))
in (

let uu____264 = (

let uu____268 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____268 replacee_term))
in (match (uu____264) with
| Some (x) -> begin
x
end
| None -> begin
(

let uu____282 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____282) with
| Some (se) -> begin
(

let uu____285 = (

let uu____286 = (FStar_ST.read in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____286))
in (match (uu____285) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end
| uu____305 -> begin
(unfold_abbrev se)
end))
end
| uu____306 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____310, quals1, attr) -> begin
(

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___198_327 -> (match (uu___198_327) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____328 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____335 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____339 = (

let uu____341 = (FStar_ST.read in_progress)
in (lid)::uu____341)
in (FStar_ST.write in_progress uu____339));
(match (()) with
| () -> begin
((remove_not_unfolded lid);
(match (()) with
| () -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_abbrev_fv lb.FStar_Syntax_Syntax.lbtyp)
in (

let tm' = (FStar_Syntax_InstFV.inst unfold_abbrev_fv lb.FStar_Syntax_Syntax.lbdef)
in (

let lb' = (

let uu___199_353 = lb
in {FStar_Syntax_Syntax.lbname = uu___199_353.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___199_353.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___199_353.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[]), (quals2), (attr)))
in ((

let uu____363 = (

let uu____365 = (FStar_ST.read rev_unfolded_type_abbrevs)
in ((

let uu___200_370 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigrng = uu___200_370.FStar_Syntax_Syntax.sigrng}))::uu____365)
in (FStar_ST.write rev_unfolded_type_abbrevs uu____363));
(match (()) with
| () -> begin
((

let uu____375 = (

let uu____377 = (FStar_ST.read in_progress)
in (FStar_List.tl uu____377))
in (FStar_ST.write in_progress uu____375));
(match (()) with
| () -> begin
tm'
end);
)
end);
)))))
end);
)
end);
)))
end
| uu____385 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____390 -> (

let uu____391 = (FStar_ST.read not_unfolded_yet)
in (match (uu____391) with
| (x)::uu____398 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____401 -> begin
(

let uu____403 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____403))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (not ((FStar_Ident.lid_equals lid lid')))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____432, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____434; FStar_Syntax_Syntax.lbtyp = uu____435; FStar_Syntax_Syntax.lbeff = uu____436; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____438, uu____439, uu____440) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (tm)
end
| uu____466 -> begin
None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____476 = (find_in_unfolded fv)
in (match (uu____476) with
| Some (t') -> begin
t'
end
| uu____485 -> begin
t
end)))
in (

let unfold_in_sig = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, bnd, ty, mut, dc, quals1) -> begin
(

let bnd' = (FStar_Syntax_InstFV.inst_binders unfold_fv bnd)
in (

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___201_512 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs1), (bnd'), (ty'), (mut'), (dc), (quals1))); FStar_Syntax_Syntax.sigrng = uu___201_512.FStar_Syntax_Syntax.sigrng}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, ty, res, npars, quals1, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___202_530 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs1), (ty'), (res), (npars), (quals1), (mut'))); FStar_Syntax_Syntax.sigrng = uu___202_530.FStar_Syntax_Syntax.sigrng}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____533, uu____534, uu____535, uu____536) -> begin
[]
end
| uu____543 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (quals), (new_members))); FStar_Syntax_Syntax.sigrng = rng}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end)))




