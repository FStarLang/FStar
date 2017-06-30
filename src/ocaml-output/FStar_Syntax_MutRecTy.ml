
open Prims
open FStar_Pervasives

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____31); FStar_Syntax_Syntax.lbunivs = uu____32; FStar_Syntax_Syntax.lbtyp = uu____33; FStar_Syntax_Syntax.lbeff = uu____34; FStar_Syntax_Syntax.lbdef = uu____35})::[]), uu____36, uu____37) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____51, uu____52, uu____53) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____59 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta}), ([]))
end
| uu____66 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____73, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____75; FStar_Syntax_Syntax.lbtyp = uu____76; FStar_Syntax_Syntax.lbeff = uu____77; FStar_Syntax_Syntax.lbdef = uu____78})::[]), uu____79, uu____80) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____98 -> begin
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

let uu____120 = (

let uu____122 = (FStar_ST.read not_unfolded_yet)
in (FStar_All.pipe_right uu____122 (FStar_List.filter (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____130, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____132; FStar_Syntax_Syntax.lbtyp = uu____133; FStar_Syntax_Syntax.lbeff = uu____134; FStar_Syntax_Syntax.lbdef = uu____135})::[]), uu____136, uu____137) -> begin
(not ((FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| uu____155 -> begin
true
end)))))
in (FStar_ST.write not_unfolded_yet uu____120)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____175, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____177; FStar_Syntax_Syntax.lbtyp = uu____178; FStar_Syntax_Syntax.lbeff = uu____179; FStar_Syntax_Syntax.lbdef = uu____180})::[]), uu____181, uu____182) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____204 -> begin
FStar_Pervasives_Native.None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____215, ({FStar_Syntax_Syntax.lbname = uu____216; FStar_Syntax_Syntax.lbunivs = uu____217; FStar_Syntax_Syntax.lbtyp = uu____218; FStar_Syntax_Syntax.lbeff = uu____219; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____221, uu____222); FStar_Syntax_Syntax.sigrng = uu____223; FStar_Syntax_Syntax.sigquals = uu____224; FStar_Syntax_Syntax.sigmeta = uu____225}) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____244 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____248 = (

let uu____252 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____252 replacee_term))
in (match (uu____248) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____266 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____266) with
| FStar_Pervasives_Native.Some (se) -> begin
(

let uu____269 = (

let uu____270 = (FStar_ST.read in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____270))
in (match (uu____269) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_Pervasives.raise (FStar_Errors.Error (((msg), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end
| uu____289 -> begin
(unfold_abbrev se)
end))
end
| uu____290 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____294, attr) -> begin
(

let quals1 = (FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals (FStar_List.filter (fun uu___178_308 -> (match (uu___178_308) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____309 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____316 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____320 = (

let uu____322 = (FStar_ST.read in_progress)
in (lid)::uu____322)
in (FStar_ST.write in_progress uu____320));
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

let uu___179_334 = lb
in {FStar_Syntax_Syntax.lbname = uu___179_334.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___179_334.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___179_334.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[]), (attr)))
in ((

let uu____343 = (

let uu____345 = (FStar_ST.read rev_unfolded_type_abbrevs)
in ((

let uu___180_350 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigrng = uu___180_350.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___180_350.FStar_Syntax_Syntax.sigmeta}))::uu____345)
in (FStar_ST.write rev_unfolded_type_abbrevs uu____343));
(match (()) with
| () -> begin
((

let uu____355 = (

let uu____357 = (FStar_ST.read in_progress)
in (FStar_List.tl uu____357))
in (FStar_ST.write in_progress uu____355));
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
| uu____365 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____370 -> (

let uu____371 = (FStar_ST.read not_unfolded_yet)
in (match (uu____371) with
| (x)::uu____378 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____381 -> begin
(

let uu____383 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____383))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (not ((FStar_Ident.lid_equals lid lid')))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____412, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____414; FStar_Syntax_Syntax.lbtyp = uu____415; FStar_Syntax_Syntax.lbeff = uu____416; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____418, uu____419) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____443 -> begin
FStar_Pervasives_Native.None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____453 = (find_in_unfolded fv)
in (match (uu____453) with
| FStar_Pervasives_Native.Some (t') -> begin
t'
end
| uu____462 -> begin
t
end)))
in (

let unfold_in_sig = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, bnd, ty, mut, dc) -> begin
(

let bnd' = (FStar_Syntax_InstFV.inst_binders unfold_fv bnd)
in (

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___181_486 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs1), (bnd'), (ty'), (mut'), (dc))); FStar_Syntax_Syntax.sigrng = uu___181_486.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___181_486.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___181_486.FStar_Syntax_Syntax.sigmeta}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, ty, res, npars, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___182_500 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs1), (ty'), (res), (npars), (mut'))); FStar_Syntax_Syntax.sigrng = uu___182_500.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___182_500.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___182_500.FStar_Syntax_Syntax.sigmeta}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____502, uu____503, uu____504) -> begin
[]
end
| uu____509 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (new_members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end)))




