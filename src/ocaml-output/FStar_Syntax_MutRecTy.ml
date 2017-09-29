
open Prims
open FStar_Pervasives

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let sigattrs = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) sigelts)
in (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____63); FStar_Syntax_Syntax.lbunivs = uu____64; FStar_Syntax_Syntax.lbtyp = uu____65; FStar_Syntax_Syntax.lbeff = uu____66; FStar_Syntax_Syntax.lbdef = uu____67})::[]), uu____68) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____87, uu____88) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____95 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}), ([]))
end
| uu____108 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____127, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____129; FStar_Syntax_Syntax.lbtyp = uu____130; FStar_Syntax_Syntax.lbeff = uu____131; FStar_Syntax_Syntax.lbdef = uu____132})::[]), uu____133) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____152 -> begin
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

let uu____181 = (

let uu____184 = (FStar_ST.op_Bang not_unfolded_yet)
in (FStar_All.pipe_right uu____184 (FStar_List.filter (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____264, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____266; FStar_Syntax_Syntax.lbtyp = uu____267; FStar_Syntax_Syntax.lbeff = uu____268; FStar_Syntax_Syntax.lbdef = uu____269})::[]), uu____270) -> begin
(not ((FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| uu____289 -> begin
true
end)))))
in (FStar_ST.op_Colon_Equals not_unfolded_yet uu____181)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____372, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____374; FStar_Syntax_Syntax.lbtyp = uu____375; FStar_Syntax_Syntax.lbeff = uu____376; FStar_Syntax_Syntax.lbdef = uu____377})::[]), uu____378) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____397 -> begin
FStar_Pervasives_Native.None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____410, ({FStar_Syntax_Syntax.lbname = uu____411; FStar_Syntax_Syntax.lbunivs = uu____412; FStar_Syntax_Syntax.lbtyp = uu____413; FStar_Syntax_Syntax.lbeff = uu____414; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____416); FStar_Syntax_Syntax.sigrng = uu____417; FStar_Syntax_Syntax.sigquals = uu____418; FStar_Syntax_Syntax.sigmeta = uu____419; FStar_Syntax_Syntax.sigattrs = uu____420}) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____449 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____454 = (

let uu____459 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____459 replacee_term))
in (match (uu____454) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____535 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____535) with
| FStar_Pervasives_Native.Some (se) -> begin
(

let uu____539 = (

let uu____540 = (FStar_ST.op_Bang in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____540))
in (match (uu____539) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_Exn.raise (FStar_Errors.Error (((msg), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end
| uu____610 -> begin
(unfold_abbrev se)
end))
end
| uu____611 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____616) -> begin
(

let quals1 = (FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals (FStar_List.filter (fun uu___215_637 -> (match (uu___215_637) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____638 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____641 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____647 = (

let uu____650 = (FStar_ST.op_Bang in_progress)
in (lid)::uu____650)
in (FStar_ST.op_Colon_Equals in_progress uu____647));
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

let uu___216_785 = lb
in {FStar_Syntax_Syntax.lbname = uu___216_785.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___216_785.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___216_785.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[])))
in ((

let uu____798 = (

let uu____801 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in ((

let uu___217_869 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigrng = uu___217_869.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___217_869.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___217_869.FStar_Syntax_Syntax.sigattrs}))::uu____801)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs uu____798));
(match (()) with
| () -> begin
((

let uu____935 = (

let uu____938 = (FStar_ST.op_Bang in_progress)
in (FStar_List.tl uu____938))
in (FStar_ST.op_Colon_Equals in_progress uu____935));
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
| uu____1069 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____1075 -> (

let uu____1076 = (FStar_ST.op_Bang not_unfolded_yet)
in (match (uu____1076) with
| (x)::uu____1146 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____1150 -> begin
(

let uu____1153 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____1153))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (not ((FStar_Ident.lid_equals lid lid')))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1260, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____1262; FStar_Syntax_Syntax.lbtyp = uu____1263; FStar_Syntax_Syntax.lbeff = uu____1264; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____1266) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____1287 -> begin
FStar_Pervasives_Native.None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____1297 = (find_in_unfolded fv)
in (match (uu____1297) with
| FStar_Pervasives_Native.Some (t') -> begin
t'
end
| uu____1307 -> begin
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

let uu___218_1340 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs1), (bnd'), (ty'), (mut'), (dc))); FStar_Syntax_Syntax.sigrng = uu___218_1340.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___218_1340.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___218_1340.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___218_1340.FStar_Syntax_Syntax.sigattrs}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, ty, res, npars, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___219_1360 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs1), (ty'), (res), (npars), (mut'))); FStar_Syntax_Syntax.sigrng = uu___219_1360.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___219_1360.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___219_1360.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___219_1360.FStar_Syntax_Syntax.sigattrs}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____1363, uu____1364) -> begin
[]
end
| uu____1369 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (new_members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end))))




