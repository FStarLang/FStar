
open Prims
open FStar_Pervasives

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let sigattrs = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) sigelts)
in (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____69); FStar_Syntax_Syntax.lbunivs = uu____70; FStar_Syntax_Syntax.lbtyp = uu____71; FStar_Syntax_Syntax.lbeff = uu____72; FStar_Syntax_Syntax.lbdef = uu____73; FStar_Syntax_Syntax.lbattrs = uu____74; FStar_Syntax_Syntax.lbpos = uu____75})::[]), uu____76) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____99, uu____100) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____107 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
(({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((sigelts), (members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}), ([]))
end
| uu____120 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____141, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____143; FStar_Syntax_Syntax.lbtyp = uu____144; FStar_Syntax_Syntax.lbeff = uu____145; FStar_Syntax_Syntax.lbdef = uu____146; FStar_Syntax_Syntax.lbattrs = uu____147; FStar_Syntax_Syntax.lbpos = uu____148})::[]), uu____149) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____172 -> begin
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

let uu____203 = (

let uu____206 = (FStar_ST.op_Bang not_unfolded_yet)
in (FStar_All.pipe_right uu____206 (FStar_List.filter (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____328, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____330; FStar_Syntax_Syntax.lbtyp = uu____331; FStar_Syntax_Syntax.lbeff = uu____332; FStar_Syntax_Syntax.lbdef = uu____333; FStar_Syntax_Syntax.lbattrs = uu____334; FStar_Syntax_Syntax.lbpos = uu____335})::[]), uu____336) -> begin
(

let uu____359 = (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (not (uu____359)))
end
| uu____360 -> begin
true
end)))))
in (FStar_ST.op_Colon_Equals not_unfolded_yet uu____203)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____490, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____492; FStar_Syntax_Syntax.lbtyp = uu____493; FStar_Syntax_Syntax.lbeff = uu____494; FStar_Syntax_Syntax.lbdef = uu____495; FStar_Syntax_Syntax.lbattrs = uu____496; FStar_Syntax_Syntax.lbpos = uu____497})::[]), uu____498) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____521 -> begin
FStar_Pervasives_Native.None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____536, ({FStar_Syntax_Syntax.lbname = uu____537; FStar_Syntax_Syntax.lbunivs = uu____538; FStar_Syntax_Syntax.lbtyp = uu____539; FStar_Syntax_Syntax.lbeff = uu____540; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____542; FStar_Syntax_Syntax.lbpos = uu____543})::[]), uu____544); FStar_Syntax_Syntax.sigrng = uu____545; FStar_Syntax_Syntax.sigquals = uu____546; FStar_Syntax_Syntax.sigmeta = uu____547; FStar_Syntax_Syntax.sigattrs = uu____548}) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____581 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____586 = (

let uu____591 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_Util.find_map uu____591 replacee_term))
in (match (uu____586) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____706 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____706) with
| FStar_Pervasives_Native.Some (se) -> begin
(

let uu____710 = (

let uu____711 = (FStar_ST.op_Bang in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) uu____711))
in (match (uu____710) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____820 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_CycleInRecTypeAbbreviation), (msg)) uu____820)))
end
| uu____821 -> begin
(unfold_abbrev se)
end))
end
| uu____822 -> begin
t
end))
end)))))
and unfold_abbrev = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____827) -> begin
(

let quals1 = (FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals (FStar_List.filter (fun uu___32_848 -> (match (uu___32_848) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____849 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____852 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((

let uu____858 = (

let uu____861 = (FStar_ST.op_Bang in_progress)
in (lid)::uu____861)
in (FStar_ST.op_Colon_Equals in_progress uu____858));
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

let uu___33_1074 = lb
in {FStar_Syntax_Syntax.lbname = uu___33_1074.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___33_1074.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___33_1074.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'; FStar_Syntax_Syntax.lbattrs = uu___33_1074.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___33_1074.FStar_Syntax_Syntax.lbpos})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), ((lid)::[])))
in ((

let uu____1087 = (

let uu____1090 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in ((

let uu___34_1197 = x
in {FStar_Syntax_Syntax.sigel = sigelt'; FStar_Syntax_Syntax.sigrng = uu___34_1197.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___34_1197.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___34_1197.FStar_Syntax_Syntax.sigattrs}))::uu____1090)
in (FStar_ST.op_Colon_Equals rev_unfolded_type_abbrevs uu____1087));
(match (()) with
| () -> begin
((

let uu____1302 = (

let uu____1305 = (FStar_ST.op_Bang in_progress)
in (FStar_List.tl uu____1305))
in (FStar_ST.op_Colon_Equals in_progress uu____1302));
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
| uu____1514 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____1522 -> (

let uu____1523 = (FStar_ST.op_Bang not_unfolded_yet)
in (match (uu____1523) with
| (x)::uu____1632 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____1636 -> begin
(

let uu____1639 = (FStar_ST.op_Bang rev_unfolded_type_abbrevs)
in (FStar_List.rev uu____1639))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (

let uu____1762 = (FStar_Ident.lid_equals lid lid')
in (not (uu____1762)))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1793, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____1795; FStar_Syntax_Syntax.lbtyp = uu____1796; FStar_Syntax_Syntax.lbeff = uu____1797; FStar_Syntax_Syntax.lbdef = tm; FStar_Syntax_Syntax.lbattrs = uu____1799; FStar_Syntax_Syntax.lbpos = uu____1800})::[]), uu____1801) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____1826 -> begin
FStar_Pervasives_Native.None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____1840 = (find_in_unfolded fv)
in (match (uu____1840) with
| FStar_Pervasives_Native.Some (t') -> begin
t'
end
| uu____1850 -> begin
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

let uu___35_1885 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univs), (bnd'), (ty'), (mut'), (dc))); FStar_Syntax_Syntax.sigrng = uu___35_1885.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___35_1885.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___35_1885.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___35_1885.FStar_Syntax_Syntax.sigattrs}))::[])))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, ty, res, npars, mut) -> begin
(

let ty' = (FStar_Syntax_InstFV.inst unfold_fv ty)
in (

let mut' = (filter_out_type_abbrevs mut)
in ((

let uu___36_1905 = x
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univs), (ty'), (res), (npars), (mut'))); FStar_Syntax_Syntax.sigrng = uu___36_1905.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___36_1905.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___36_1905.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___36_1905.FStar_Syntax_Syntax.sigattrs}))::[]))
end
| FStar_Syntax_Syntax.Sig_let (uu____1908, uu____1909) -> begin
[]
end
| uu____1914 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (new_members))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = sigattrs}
in ((new_bundle), (unfolded_type_abbrevs))))))))
end))))




