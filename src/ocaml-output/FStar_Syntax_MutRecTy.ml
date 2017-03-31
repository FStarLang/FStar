
open Prims

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.fsdoc Prims.option  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng doc1 -> (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____36); FStar_Syntax_Syntax.lbunivs = uu____37; FStar_Syntax_Syntax.lbtyp = uu____38; FStar_Syntax_Syntax.lbeff = uu____39; FStar_Syntax_Syntax.lbdef = uu____40})::[]), uu____41, uu____42, uu____43) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____59, uu____60, uu____61, uu____62) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____70 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (quals), (members))); FStar_Syntax_Syntax.sigdoc = doc1; FStar_Syntax_Syntax.sigrng = rng}), ([]))
end
| uu____78 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____85, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____87; FStar_Syntax_Syntax.lbtyp = uu____88; FStar_Syntax_Syntax.lbeff = uu____89; FStar_Syntax_Syntax.lbdef = uu____90})::[]), uu____91, uu____92, uu____93) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____113 -> begin
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

let uu____135 = (

let uu____137 = (FStar_ST.read not_unfolded_yet)
in (FStar_All.pipe_right uu____137 (FStar_List.filter (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____145, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____147; FStar_Syntax_Syntax.lbtyp = uu____148; FStar_Syntax_Syntax.lbeff = uu____149; FStar_Syntax_Syntax.lbdef = uu____150})::[]), uu____151, uu____152, uu____153) -> begin
(not ((FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| uu____173 -> begin
true
end)))))
in (FStar_ST.write not_unfolded_yet uu____135)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____193, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____195; FStar_Syntax_Syntax.lbtyp = uu____196; FStar_Syntax_Syntax.lbeff = uu____197; FStar_Syntax_Syntax.lbdef = uu____198})::[]), uu____199, uu____200, uu____201) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (x)
end
| uu____225 -> begin
None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____236, ({FStar_Syntax_Syntax.lbname = uu____237; FStar_Syntax_Syntax.lbunivs = uu____238; FStar_Syntax_Syntax.lbtyp = uu____239; FStar_Syntax_Syntax.lbeff = uu____240; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____242, uu____243, uu____244); FStar_Syntax_Syntax.sigdoc = uu____245; FStar_Syntax_Syntax.sigrng = uu____246}) -> begin
Some (tm)
end
| uu____267 -> begin
None
end))
in (

let uu____271 = (

let uu____275 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____275 replacee_term))
in (match (uu____271) with
| Some (x) -> begin
x
end
| None -> begin
(

let uu____289 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____289) with
| Some (se) -> begin
(

let uu____292 = (

let uu____293 = (FStar_ST.read in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____293))
in (match (uu____292) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end
| uu____312 -> begin
(unfold_abbrev se)
end))
end
| uu____313 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____317, quals1, attr) -> begin
(

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___198_334 -> (match (uu___198_334) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____335 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____342 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____346 = (

let uu____348 = (FStar_ST.read in_progress)
in (lid)::uu____348)
in (FStar_ST.write in_progress uu____346));
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

let uu___199_360 = lb
in {FStar_Syntax_Syntax.lbname = uu___199_360.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___199_360.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___199_360.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[]), (quals2), (attr)))
in ((

let uu____370 = (

let uu____372 = (FStar_ST.read rev_unfolded_type_abbrevs)
in ((

let uu___200_377 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigdoc = uu___200_377.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___200_377.FStar_Syntax_Syntax.sigrng}))::uu____372)
in (FStar_ST.write rev_unfolded_type_abbrevs uu____370));
(match (()) with
| () -> begin
((

let uu____382 = (

let uu____384 = (FStar_ST.read in_progress)
in (FStar_List.tl uu____384))
in (FStar_ST.write in_progress uu____382));
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
| uu____392 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____397 -> (

let uu____398 = (FStar_ST.read not_unfolded_yet)
in (match (uu____398) with
| (x)::uu____405 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____408 -> begin
(

let uu____410 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____410))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (not ((FStar_Ident.lid_equals lid lid')))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____439, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____441; FStar_Syntax_Syntax.lbtyp = uu____442; FStar_Syntax_Syntax.lbeff = uu____443; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____445, uu____446, uu____447) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (tm)
end
| uu____473 -> begin
None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____483 = (find_in_unfolded fv)
in (match (uu____483) with
| Some (t') -> begin
t'
end
| uu____492 -> begin
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

let uu___201_519 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs1), (bnd'), (ty'), (mut'), (dc), (quals1))); FStar_Syntax_Syntax.sigdoc = uu___201_519.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___201_519.FStar_Syntax_Syntax.sigrng}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, ty, res, npars, quals1, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___202_537 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs1), (ty'), (res), (npars), (quals1), (mut'))); FStar_Syntax_Syntax.sigdoc = uu___202_537.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___202_537.FStar_Syntax_Syntax.sigrng}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____540, uu____541, uu____542, uu____543) -> begin
[]
end
| uu____550 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (quals), (new_members))); FStar_Syntax_Syntax.sigdoc = doc1; FStar_Syntax_Syntax.sigrng = rng}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end)))




