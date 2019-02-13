
open Prims
open FStar_Pervasives

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let sigattrs = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) sigelts)
in (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____69); FStar_Syntax_Syntax.lbunivs = uu____70; FStar_Syntax_Syntax.lbtyp = uu____71; FStar_Syntax_Syntax.lbeff = uu____72; FStar_Syntax_Syntax.lbdef = uu____73; FStar_Syntax_Syntax.lbattrs = uu____74; FStar_Syntax_Syntax.lbpos = uu____75})::[]), uu____76) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____95, uu____96) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____104 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}), ([]))
end
| uu____117 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____138, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____140; FStar_Syntax_Syntax.lbtyp = uu____141; FStar_Syntax_Syntax.lbeff = uu____142; FStar_Syntax_Syntax.lbdef = uu____143; FStar_Syntax_Syntax.lbattrs = uu____144; FStar_Syntax_Syntax.lbpos = uu____145})::[]), uu____146) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____165 -> begin
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

let uu____197 = (

let uu____200 = (FStar_ST.op_Bang not_unfolded_yet)
in (FStar_All.pipe_right uu____200 (FStar_List.filter (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____265, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____267; FStar_Syntax_Syntax.lbtyp = uu____268; FStar_Syntax_Syntax.lbeff = uu____269; FStar_Syntax_Syntax.lbdef = uu____270; FStar_Syntax_Syntax.lbattrs = uu____271; FStar_Syntax_Syntax.lbpos = uu____272})::[]), uu____273) -> begin
(

let uu____292 = (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (not (uu____292)))
end
| uu____294 -> begin
true
end)))))
in (FStar_ST.op_Colon_Equals not_unfolded_yet uu____197)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____367, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____369; FStar_Syntax_Syntax.lbtyp = uu____370; FStar_Syntax_Syntax.lbeff = uu____371; FStar_Syntax_Syntax.lbdef = uu____372; FStar_Syntax_Syntax.lbattrs = uu____373; FStar_Syntax_Syntax.lbpos = uu____374})::[]), uu____375) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____394 -> begin
FStar_Pervasives_Native.None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____409, ({FStar_Syntax_Syntax.lbname = uu____410; FStar_Syntax_Syntax.lbunivs = uu____411; FStar_Syntax_Syntax.lbtyp = uu____412; FStar_Syntax_Syntax.lbeff = uu____413; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____415; FStar_Syntax_Syntax.lbpos = uu____416})::[]), uu____417); FStar_Syntax_Syntax.sigrng = uu____418; FStar_Syntax_Syntax.sigquals = uu____419; FStar_Syntax_Syntax.sigmeta = uu____420; FStar_Syntax_Syntax.sigattrs = uu____421}) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____450 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____455 = (

let uu____460 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____460 replacee_term))
in (match (uu____455) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____517 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____517) with
| FStar_Pervasives_Native.Some (se) -> begin
(

let uu____521 = (

let uu____523 = (FStar_ST.op_Bang in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____523))
in (match (uu____521) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____577 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_CycleInRecTypeAbbreviation), (msg)) uu____577)))
end
| uu____579 -> begin
(unfold_abbrev se)
end))
end
| uu____581 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____586) -> begin
(

let quals1 = (FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals (FStar_List.filter (fun uu___101_603 -> (match (uu___101_603) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____606 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____610 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____617 = (

let uu____620 = (FStar_ST.op_Bang in_progress)
in (lid)::uu____620)
in (FStar_ST.op_Colon_Equals in_progress uu____617));
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

let uu___102_717 = lb
in {FStar_Syntax_Syntax.lbname = uu___102_717.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___102_717.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___102_717.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'; FStar_Syntax_Syntax.lbattrs = uu___102_717.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___102_717.FStar_Syntax_Syntax.lbpos})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[])))
in ((

let uu____726 = (

let uu____729 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in ((

let uu___103_778 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigrng = uu___103_778.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___103_778.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___103_778.FStar_Syntax_Syntax.sigattrs}))::uu____729)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs uu____726));
(match (()) with
| () -> begin
((

let uu____825 = (

let uu____828 = (FStar_ST.op_Bang in_progress)
in (FStar_List.tl uu____828))
in (FStar_ST.op_Colon_Equals in_progress uu____825));
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
| uu____921 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____930 -> (

let uu____931 = (FStar_ST.op_Bang not_unfolded_yet)
in (match (uu____931) with
| (x)::uu____982 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____986 -> begin
(

let uu____989 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____989))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (

let uu____1054 = (FStar_Ident.lid_equals lid lid')
in (not (uu____1054)))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1086, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____1088; FStar_Syntax_Syntax.lbtyp = uu____1089; FStar_Syntax_Syntax.lbeff = uu____1090; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____1092; FStar_Syntax_Syntax.lbpos = uu____1093})::[]), uu____1094) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____1115 -> begin
FStar_Pervasives_Native.None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____1129 = (find_in_unfolded fv)
in (match (uu____1129) with
| FStar_Pervasives_Native.Some (t') -> begin
t'
end
| uu____1139 -> begin
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

let uu___104_1174 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs), (bnd'), (ty'), (mut'), (dc))); FStar_Syntax_Syntax.sigrng = uu___104_1174.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___104_1174.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___104_1174.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___104_1174.FStar_Syntax_Syntax.sigattrs}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, ty, res, npars, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___105_1196 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs), (ty'), (res), (npars), (mut'))); FStar_Syntax_Syntax.sigrng = uu___105_1196.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___105_1196.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___105_1196.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___105_1196.FStar_Syntax_Syntax.sigattrs}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____1200, uu____1201) -> begin
[]
end
| uu____1206 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (new_members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end))))




