
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
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}), ([]))
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
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____364, ({FStar_Syntax_Syntax.lbname = uu____365; FStar_Syntax_Syntax.lbunivs = uu____366; FStar_Syntax_Syntax.lbtyp = uu____367; FStar_Syntax_Syntax.lbeff = uu____368; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____370; FStar_Syntax_Syntax.lbpos = uu____371})::[]), uu____372); FStar_Syntax_Syntax.sigrng = uu____373; FStar_Syntax_Syntax.sigquals = uu____374; FStar_Syntax_Syntax.sigmeta = uu____375; FStar_Syntax_Syntax.sigattrs = uu____376; FStar_Syntax_Syntax.sigopts = uu____377}) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____408 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____413 = (

let uu____418 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____418 replacee_term))
in (match (uu____413) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____453 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____453) with
| FStar_Pervasives_Native.Some (se) -> begin
(

let uu____457 = (

let uu____459 = (FStar_ST.op_Bang in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____459))
in (match (uu____457) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____491 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_CycleInRecTypeAbbreviation), (msg)) uu____491)))
end
| uu____493 -> begin
(unfold_abbrev se)
end))
end
| uu____495 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____500) -> begin
(

let quals1 = (FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals (FStar_List.filter (fun uu___0_517 -> (match (uu___0_517) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____520 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____524 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____531 = (

let uu____534 = (FStar_ST.op_Bang in_progress)
in (lid)::uu____534)
in (FStar_ST.op_Colon_Equals in_progress uu____531));
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

let uu___146_587 = lb
in {FStar_Syntax_Syntax.lbname = uu___146_587.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___146_587.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___146_587.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'; FStar_Syntax_Syntax.lbattrs = uu___146_587.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___146_587.FStar_Syntax_Syntax.lbpos})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[])))
in ((

let uu____596 = (

let uu____599 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in ((

let uu___150_626 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigrng = uu___150_626.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___150_626.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___150_626.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___150_626.FStar_Syntax_Syntax.sigopts}))::uu____599)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs uu____596));
(match (()) with
| () -> begin
((

let uu____651 = (

let uu____654 = (FStar_ST.op_Bang in_progress)
in (FStar_List.tl uu____654))
in (FStar_ST.op_Colon_Equals in_progress uu____651));
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
| uu____703 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____712 -> (

let uu____713 = (FStar_ST.op_Bang not_unfolded_yet)
in (match (uu____713) with
| (x)::uu____742 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____746 -> begin
(

let uu____749 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____749))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (

let uu____792 = (FStar_Ident.lid_equals lid lid')
in (not (uu____792)))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____824, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____826; FStar_Syntax_Syntax.lbtyp = uu____827; FStar_Syntax_Syntax.lbeff = uu____828; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____830; FStar_Syntax_Syntax.lbpos = uu____831})::[]), uu____832) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____853 -> begin
FStar_Pervasives_Native.None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____867 = (find_in_unfolded fv)
in (match (uu____867) with
| FStar_Pervasives_Native.Some (t') -> begin
t'
end
| uu____877 -> begin
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

let uu___205_912 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs), (bnd'), (ty'), (mut'), (dc))); FStar_Syntax_Syntax.sigrng = uu___205_912.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___205_912.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___205_912.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___205_912.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___205_912.FStar_Syntax_Syntax.sigopts}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, ty, res, npars, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___217_934 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs), (ty'), (res), (npars), (mut'))); FStar_Syntax_Syntax.sigrng = uu___217_934.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___217_934.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___217_934.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___217_934.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___217_934.FStar_Syntax_Syntax.sigopts}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____938, uu____939) -> begin
[]
end
| uu____944 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (new_members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end))))




