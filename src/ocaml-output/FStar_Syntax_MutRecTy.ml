
open Prims
open FStar_Pervasives

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let sigattrs = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) sigelts)
in (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____68); FStar_Syntax_Syntax.lbunivs = uu____69; FStar_Syntax_Syntax.lbtyp = uu____70; FStar_Syntax_Syntax.lbeff = uu____71; FStar_Syntax_Syntax.lbdef = uu____72; FStar_Syntax_Syntax.lbattrs = uu____73; FStar_Syntax_Syntax.lbpos = uu____74})::[]), uu____75) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____94, uu____95) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____103 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}), ([]))
end
| uu____116 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____137, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____139; FStar_Syntax_Syntax.lbtyp = uu____140; FStar_Syntax_Syntax.lbeff = uu____141; FStar_Syntax_Syntax.lbdef = uu____142; FStar_Syntax_Syntax.lbattrs = uu____143; FStar_Syntax_Syntax.lbpos = uu____144})::[]), uu____145) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____164 -> begin
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

let uu____196 = (

let uu____199 = (FStar_ST.op_Bang not_unfolded_yet)
in (FStar_All.pipe_right uu____199 (FStar_List.filter (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____242, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____244; FStar_Syntax_Syntax.lbtyp = uu____245; FStar_Syntax_Syntax.lbeff = uu____246; FStar_Syntax_Syntax.lbdef = uu____247; FStar_Syntax_Syntax.lbattrs = uu____248; FStar_Syntax_Syntax.lbpos = uu____249})::[]), uu____250) -> begin
(

let uu____269 = (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (not (uu____269)))
end
| uu____271 -> begin
true
end)))))
in (FStar_ST.op_Colon_Equals not_unfolded_yet uu____196)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____322, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____324; FStar_Syntax_Syntax.lbtyp = uu____325; FStar_Syntax_Syntax.lbeff = uu____326; FStar_Syntax_Syntax.lbdef = uu____327; FStar_Syntax_Syntax.lbattrs = uu____328; FStar_Syntax_Syntax.lbpos = uu____329})::[]), uu____330) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____349 -> begin
FStar_Pervasives_Native.None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____364, ({FStar_Syntax_Syntax.lbname = uu____365; FStar_Syntax_Syntax.lbunivs = uu____366; FStar_Syntax_Syntax.lbtyp = uu____367; FStar_Syntax_Syntax.lbeff = uu____368; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____370; FStar_Syntax_Syntax.lbpos = uu____371})::[]), uu____372); FStar_Syntax_Syntax.sigrng = uu____373; FStar_Syntax_Syntax.sigquals = uu____374; FStar_Syntax_Syntax.sigmeta = uu____375; FStar_Syntax_Syntax.sigattrs = uu____376}) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____405 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____410 = (

let uu____415 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____415 replacee_term))
in (match (uu____410) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____450 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____450) with
| FStar_Pervasives_Native.Some (se) -> begin
(

let uu____454 = (

let uu____456 = (FStar_ST.op_Bang in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____456))
in (match (uu____454) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____488 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_CycleInRecTypeAbbreviation), (msg)) uu____488)))
end
| uu____490 -> begin
(unfold_abbrev se)
end))
end
| uu____492 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____497) -> begin
(

let quals1 = (FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals (FStar_List.filter (fun uu___0_514 -> (match (uu___0_514) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____517 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____521 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____528 = (

let uu____531 = (FStar_ST.op_Bang in_progress)
in (lid)::uu____531)
in (FStar_ST.op_Colon_Equals in_progress uu____528));
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

let uu___145_584 = lb
in {FStar_Syntax_Syntax.lbname = uu___145_584.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___145_584.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___145_584.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'; FStar_Syntax_Syntax.lbattrs = uu___145_584.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___145_584.FStar_Syntax_Syntax.lbpos})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[])))
in ((

let uu____593 = (

let uu____596 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in ((

let uu___149_623 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigrng = uu___149_623.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___149_623.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___149_623.FStar_Syntax_Syntax.sigattrs}))::uu____596)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs uu____593));
(match (()) with
| () -> begin
((

let uu____648 = (

let uu____651 = (FStar_ST.op_Bang in_progress)
in (FStar_List.tl uu____651))
in (FStar_ST.op_Colon_Equals in_progress uu____648));
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
| uu____700 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____709 -> (

let uu____710 = (FStar_ST.op_Bang not_unfolded_yet)
in (match (uu____710) with
| (x)::uu____739 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____743 -> begin
(

let uu____746 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____746))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (

let uu____789 = (FStar_Ident.lid_equals lid lid')
in (not (uu____789)))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____821, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____823; FStar_Syntax_Syntax.lbtyp = uu____824; FStar_Syntax_Syntax.lbeff = uu____825; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____827; FStar_Syntax_Syntax.lbpos = uu____828})::[]), uu____829) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____850 -> begin
FStar_Pervasives_Native.None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____864 = (find_in_unfolded fv)
in (match (uu____864) with
| FStar_Pervasives_Native.Some (t') -> begin
t'
end
| uu____874 -> begin
t
end)))
in (

let unfold_in_sig = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, bnd, ty, mut, dc) -> begin
(

let bnd' = (FStar_Syntax_InstFV.inst_binders unfold_fv bnd)
in (

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___204_909 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs), (bnd'), (ty'), (mut'), (dc))); FStar_Syntax_Syntax.sigrng = uu___204_909.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___204_909.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___204_909.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___204_909.FStar_Syntax_Syntax.sigattrs}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, ty, res, npars, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___216_931 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs), (ty'), (res), (npars), (mut'))); FStar_Syntax_Syntax.sigrng = uu___216_931.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___216_931.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___216_931.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___216_931.FStar_Syntax_Syntax.sigattrs}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____935, uu____936) -> begin
[]
end
| uu____941 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (new_members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end))))




