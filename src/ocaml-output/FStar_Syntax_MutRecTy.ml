
open Prims
open FStar_Pervasives

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let sigattrs = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) sigelts)
in (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____69); FStar_Syntax_Syntax.lbunivs = uu____70; FStar_Syntax_Syntax.lbtyp = uu____71; FStar_Syntax_Syntax.lbeff = uu____72; FStar_Syntax_Syntax.lbdef = uu____73; FStar_Syntax_Syntax.lbattrs = uu____74; FStar_Syntax_Syntax.lbpos = uu____75})::[]), uu____76) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____93, uu____94) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____101 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}), ([]))
end
| uu____114 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____135, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____137; FStar_Syntax_Syntax.lbtyp = uu____138; FStar_Syntax_Syntax.lbeff = uu____139; FStar_Syntax_Syntax.lbdef = uu____140; FStar_Syntax_Syntax.lbattrs = uu____141; FStar_Syntax_Syntax.lbpos = uu____142})::[]), uu____143) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____160 -> begin
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

let uu____191 = (

let uu____194 = (FStar_ST.op_Bang not_unfolded_yet)
in (FStar_All.pipe_right uu____194 (FStar_List.filter (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____262, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____264; FStar_Syntax_Syntax.lbtyp = uu____265; FStar_Syntax_Syntax.lbeff = uu____266; FStar_Syntax_Syntax.lbdef = uu____267; FStar_Syntax_Syntax.lbattrs = uu____268; FStar_Syntax_Syntax.lbpos = uu____269})::[]), uu____270) -> begin
(

let uu____287 = (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (not (uu____287)))
end
| uu____288 -> begin
true
end)))))
in (FStar_ST.op_Colon_Equals not_unfolded_yet uu____191)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____364, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____366; FStar_Syntax_Syntax.lbtyp = uu____367; FStar_Syntax_Syntax.lbeff = uu____368; FStar_Syntax_Syntax.lbdef = uu____369; FStar_Syntax_Syntax.lbattrs = uu____370; FStar_Syntax_Syntax.lbpos = uu____371})::[]), uu____372) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____389 -> begin
FStar_Pervasives_Native.None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____404, ({FStar_Syntax_Syntax.lbname = uu____405; FStar_Syntax_Syntax.lbunivs = uu____406; FStar_Syntax_Syntax.lbtyp = uu____407; FStar_Syntax_Syntax.lbeff = uu____408; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____410; FStar_Syntax_Syntax.lbpos = uu____411})::[]), uu____412); FStar_Syntax_Syntax.sigrng = uu____413; FStar_Syntax_Syntax.sigquals = uu____414; FStar_Syntax_Syntax.sigmeta = uu____415; FStar_Syntax_Syntax.sigattrs = uu____416}) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____443 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____448 = (

let uu____453 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____453 replacee_term))
in (match (uu____448) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____514 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____514) with
| FStar_Pervasives_Native.Some (se) -> begin
(

let uu____518 = (

let uu____519 = (FStar_ST.op_Bang in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____519))
in (match (uu____518) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____574 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_CycleInRecTypeAbbreviation), (msg)) uu____574)))
end
| uu____575 -> begin
(unfold_abbrev se)
end))
end
| uu____576 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____581) -> begin
(

let quals1 = (FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals (FStar_List.filter (fun uu___29_596 -> (match (uu___29_596) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____597 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____600 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____606 = (

let uu____609 = (FStar_ST.op_Bang in_progress)
in (lid)::uu____609)
in (FStar_ST.op_Colon_Equals in_progress uu____606));
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

let uu___30_714 = lb
in {FStar_Syntax_Syntax.lbname = uu___30_714.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___30_714.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___30_714.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'; FStar_Syntax_Syntax.lbattrs = uu___30_714.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___30_714.FStar_Syntax_Syntax.lbpos})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[])))
in ((

let uu____721 = (

let uu____724 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in ((

let uu___31_777 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigrng = uu___31_777.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___31_777.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___31_777.FStar_Syntax_Syntax.sigattrs}))::uu____724)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs uu____721));
(match (()) with
| () -> begin
((

let uu____828 = (

let uu____831 = (FStar_ST.op_Bang in_progress)
in (FStar_List.tl uu____831))
in (FStar_ST.op_Colon_Equals in_progress uu____828));
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
| uu____932 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____940 -> (

let uu____941 = (FStar_ST.op_Bang not_unfolded_yet)
in (match (uu____941) with
| (x)::uu____996 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____1000 -> begin
(

let uu____1003 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____1003))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (

let uu____1072 = (FStar_Ident.lid_equals lid lid')
in (not (uu____1072)))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1103, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____1105; FStar_Syntax_Syntax.lbtyp = uu____1106; FStar_Syntax_Syntax.lbeff = uu____1107; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____1109; FStar_Syntax_Syntax.lbpos = uu____1110})::[]), uu____1111) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____1130 -> begin
FStar_Pervasives_Native.None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____1144 = (find_in_unfolded fv)
in (match (uu____1144) with
| FStar_Pervasives_Native.Some (t') -> begin
t'
end
| uu____1154 -> begin
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

let uu___32_1189 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs), (bnd'), (ty'), (mut'), (dc))); FStar_Syntax_Syntax.sigrng = uu___32_1189.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___32_1189.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___32_1189.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___32_1189.FStar_Syntax_Syntax.sigattrs}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, ty, res, npars, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___33_1209 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs), (ty'), (res), (npars), (mut'))); FStar_Syntax_Syntax.sigrng = uu___33_1209.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___33_1209.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___33_1209.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___33_1209.FStar_Syntax_Syntax.sigattrs}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____1212, uu____1213) -> begin
[]
end
| uu____1218 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (new_members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end))))




