
open Prims

let disentangle_abbrevs_from_bundle : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun sigelts quals members rng -> (

let type_abbrev_sigelts = (FStar_All.pipe_right sigelts (FStar_List.collect (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____31); FStar_Syntax_Syntax.lbunivs = uu____32; FStar_Syntax_Syntax.lbtyp = uu____33; FStar_Syntax_Syntax.lbeff = uu____34; FStar_Syntax_Syntax.lbdef = uu____35})::[]), uu____36, uu____37, uu____38, uu____39) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Sig_let (uu____55, uu____56, uu____57, uu____58, uu____59) -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible")
end
| uu____67 -> begin
[]
end))))
in (match (type_abbrev_sigelts) with
| [] -> begin
((FStar_Syntax_Syntax.Sig_bundle (((sigelts), (quals), (members), (rng)))), ([]))
end
| uu____75 -> begin
(

let type_abbrevs = (FStar_All.pipe_right type_abbrev_sigelts (FStar_List.map (fun uu___199_81 -> (match (uu___199_81) with
| FStar_Syntax_Syntax.Sig_let ((uu____82, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____84; FStar_Syntax_Syntax.lbtyp = uu____85; FStar_Syntax_Syntax.lbeff = uu____86; FStar_Syntax_Syntax.lbdef = uu____87})::[]), uu____88, uu____89, uu____90, uu____91) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____111 -> begin
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

let remove_not_unfolded = (fun lid -> (let _0_705 = (let _0_704 = (FStar_ST.read not_unfolded_yet)
in (FStar_All.pipe_right _0_704 (FStar_List.filter (fun uu___200_141 -> (match (uu___200_141) with
| FStar_Syntax_Syntax.Sig_let ((uu____142, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____144; FStar_Syntax_Syntax.lbtyp = uu____145; FStar_Syntax_Syntax.lbeff = uu____146; FStar_Syntax_Syntax.lbdef = uu____147})::[]), uu____148, uu____149, uu____150, uu____151) -> begin
(not ((FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| uu____171 -> begin
true
end)))))
in (FStar_ST.write not_unfolded_yet _0_705)))
in (

let rec unfold_abbrev_fv = (fun t fv -> (

let replacee = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((uu____188, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____190; FStar_Syntax_Syntax.lbtyp = uu____191; FStar_Syntax_Syntax.lbeff = uu____192; FStar_Syntax_Syntax.lbdef = uu____193})::[]), uu____194, uu____195, uu____196, uu____197) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (x)
end
| uu____221 -> begin
None
end))
in (

let replacee_term = (fun x -> (match ((replacee x)) with
| Some (FStar_Syntax_Syntax.Sig_let ((uu____232, ({FStar_Syntax_Syntax.lbname = uu____233; FStar_Syntax_Syntax.lbunivs = uu____234; FStar_Syntax_Syntax.lbtyp = uu____235; FStar_Syntax_Syntax.lbeff = uu____236; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____238, uu____239, uu____240, uu____241)) -> begin
Some (tm)
end
| uu____261 -> begin
None
end))
in (

let uu____265 = (let _0_706 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (FStar_Util.find_map _0_706 replacee_term))
in (match (uu____265) with
| Some (x) -> begin
x
end
| None -> begin
(

let uu____281 = (FStar_Util.find_map type_abbrev_sigelts replacee)
in (match (uu____281) with
| Some (se) -> begin
(

let uu____284 = (let _0_707 = (FStar_ST.read in_progress)
in (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) _0_707))
in (match (uu____284) with
| true -> begin
(

let msg = (FStar_Util.format1 "Cycle on %s in mutually recursive type abbreviations" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end
| uu____302 -> begin
(unfold_abbrev se)
end))
end
| uu____303 -> begin
t
end))
end)))))
and unfold_abbrev = (fun uu___202_305 -> (match (uu___202_305) with
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), rng, uu____308, quals, attr) -> begin
(

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___201_325 -> (match (uu___201_325) with
| FStar_Syntax_Syntax.Noeq -> begin
false
end
| uu____326 -> begin
true
end))))
in (

let lid = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____333 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible")
end)
in ((let _0_709 = (let _0_708 = (FStar_ST.read in_progress)
in (lid)::_0_708)
in (FStar_ST.write in_progress _0_709));
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

let uu___204_347 = lb
in {FStar_Syntax_Syntax.lbname = uu___204_347.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___204_347.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty'; FStar_Syntax_Syntax.lbeff = uu___204_347.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (

let sigelt' = FStar_Syntax_Syntax.Sig_let (((((false), ((lb')::[]))), (rng), ((lid)::[]), (quals), (attr)))
in ((let _0_711 = (let _0_710 = (FStar_ST.read rev_unfolded_type_abbrevs)
in (sigelt')::_0_710)
in (FStar_ST.write rev_unfolded_type_abbrevs _0_711));
(match (()) with
| () -> begin
((let _0_712 = (FStar_List.tl (FStar_ST.read in_progress))
in (FStar_ST.write in_progress _0_712));
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
| uu____370 -> begin
(failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible")
end))
in (

let rec aux = (fun uu____375 -> (

let uu____376 = (FStar_ST.read not_unfolded_yet)
in (match (uu____376) with
| (x)::uu____383 -> begin
(

let _unused = (unfold_abbrev x)
in (aux ()))
end
| uu____386 -> begin
(FStar_List.rev (FStar_ST.read rev_unfolded_type_abbrevs))
end)))
in (aux ())))))))
in (

let filter_out_type_abbrevs = (fun l -> (FStar_List.filter (fun lid -> (FStar_List.for_all (fun lid' -> (not ((FStar_Ident.lid_equals lid lid')))) type_abbrevs)) l))
in (

let inductives_with_abbrevs_unfolded = (

let find_in_unfolded = (fun fv -> (FStar_Util.find_map unfolded_type_abbrevs (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((uu____415, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv'); FStar_Syntax_Syntax.lbunivs = uu____417; FStar_Syntax_Syntax.lbtyp = uu____418; FStar_Syntax_Syntax.lbeff = uu____419; FStar_Syntax_Syntax.lbdef = tm})::[]), uu____421, uu____422, uu____423, uu____424) when (FStar_Ident.lid_equals fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
Some (tm)
end
| uu____450 -> begin
None
end))))
in (

let unfold_fv = (fun t fv -> (

let uu____460 = (find_in_unfolded fv)
in (match (uu____460) with
| Some (t') -> begin
t'
end
| uu____469 -> begin
t
end)))
in (

let unfold_in_sig = (fun uu___203_477 -> (match (uu___203_477) with
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
| FStar_Syntax_Syntax.Sig_let (uu____517, uu____518, uu____519, uu____520, uu____521) -> begin
[]
end
| uu____528 -> begin
(failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible")
end))
in (FStar_List.collect unfold_in_sig sigelts))))
in (

let new_members = (filter_out_type_abbrevs members)
in (

let new_bundle = FStar_Syntax_Syntax.Sig_bundle (((inductives_with_abbrevs_unfolded), (quals), (new_members), (rng)))
in ((new_bundle), (unfolded_type_abbrevs))))))))
end)))




