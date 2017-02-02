
open Prims

let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface impl -> (

let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (

let is_val = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, uu____28) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____29 -> begin
false
end))
in (

let is_type = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____37, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun uu____54 -> (match (uu____54) with
| (t, uu____59) -> begin
((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText)
end))))
end
| uu____62 -> begin
false
end))
in (

let is_let = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____70, defs) -> begin
(

let uu____78 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right uu____78 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (uu____81, tys) -> begin
(

let uu____91 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____101 -> (match (uu____101) with
| (x, uu____106) -> begin
x
end))))
in (FStar_All.pipe_right uu____91 (FStar_Util.for_some (fun uu___140_110 -> (match (uu___140_110) with
| FStar_Parser_AST.TyconAbbrev (id', uu____112, uu____113, uu____114) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| uu____119 -> begin
false
end)))))
end
| uu____120 -> begin
false
end))
in (

let prefix_until_let = (fun x ds -> (FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))))
in (

let aux_ml = (fun iface impl -> (

let rec interleave_vals = (fun vals impl -> (match (vals) with
| [] -> begin
impl
end
| ({FStar_Parser_AST.d = FStar_Parser_AST.Val (x, uu____170); FStar_Parser_AST.drange = uu____171; FStar_Parser_AST.doc = uu____172; FStar_Parser_AST.quals = uu____173; FStar_Parser_AST.attrs = uu____174})::remaining_vals -> begin
(

let d = (FStar_List.hd vals)
in (

let lopt = (prefix_until_let x impl)
in (match (lopt) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "No definition found for " x.FStar_Ident.idText)), (d.FStar_Parser_AST.drange)))))
end
| Some (prefix, let_x, rest_impl) -> begin
(

let impl = (FStar_List.append prefix (FStar_List.append ((d)::(let_x)::[]) rest_impl))
in (interleave_vals remaining_vals impl))
end)))
end
| (uu____207)::remaining_vals -> begin
(interleave_vals remaining_vals impl)
end))
in (interleave_vals iface impl)))
in (

let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(

let uu____230 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append uu____230 impl))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____240, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___141_257 -> (match (uu___141_257) with
| (FStar_Parser_AST.TyconAbstract (uu____261), uu____262) -> begin
true
end
| uu____270 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Errors.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
((

let uu____278 = (FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))
in (match (uu____278) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (uu____283); FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = uu____285; FStar_Parser_AST.quals = uu____286; FStar_Parser_AST.attrs = uu____287}) -> begin
(

let uu____291 = (

let uu____292 = (

let uu____295 = (

let uu____296 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" uu____296))
in ((uu____295), (r)))
in FStar_Errors.Error (uu____292))
in (Prims.raise uu____291))
end
| Some (i) -> begin
(

let uu____298 = (

let uu____299 = (

let uu____302 = (

let uu____303 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" uu____303))
in ((uu____302), (i.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____299))
in (Prims.raise uu____298))
end));
(

let uu____304 = (prefix_until_let x iface)
in (match (uu____304) with
| Some (uu____312) -> begin
(

let uu____323 = (

let uu____324 = (

let uu____327 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((uu____327), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____324))
in (Prims.raise uu____323))
end
| None -> begin
(

let lopt = (prefix_until_let x impl)
in (match (lopt) with
| None -> begin
(

let uu____347 = (FStar_All.pipe_right d.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____347) with
| true -> begin
(aux (((d)::[])::out) ds impl)
end
| uu____350 -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "No definition found for " x.FStar_Ident.idText)), (d.FStar_Parser_AST.drange)))))
end))
end
| Some (prefix, let_x, rest_impl) -> begin
(

let uu____364 = (FStar_All.pipe_right d.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____364) with
| true -> begin
(

let uu____366 = (

let uu____367 = (

let uu____370 = (

let uu____371 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText uu____371))
in ((uu____370), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____367))
in (Prims.raise uu____366))
end
| uu____373 -> begin
(

let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (x, uu____381) -> begin
(x)::[]
end
| uu____382 -> begin
[]
end))))
in (

let uu____383 = (FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))
in (match (uu____383) with
| Some (d) -> begin
(

let uu____392 = (

let uu____393 = (

let uu____396 = (

let uu____397 = (FStar_Parser_AST.decl_to_string d)
in (

let uu____398 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" uu____397 uu____398)))
in ((uu____396), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____393))
in (Prims.raise uu____392))
end
| uu____400 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____403, defs) -> begin
(

let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (

let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, uu____429) -> begin
(

let uu____430 = (FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))
in (not (uu____430)))
end
| uu____432 -> begin
true
end))))
in (

let uu____433 = (match (iface_prefix_opt) with
| None -> begin
((iface), ([]))
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
((all_vals_for_defs), ((first_non_val)::rest_iface))
end)
in (match (uu____433) with
| (all_vals_for_defs, rest_iface) -> begin
(

let hoist = (FStar_List.append prefix (FStar_List.append all_vals_for_defs ((let_x)::[])))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| uu____473 -> begin
(failwith "Impossible")
end)
end)))
end))
end))
end));
)
end
| uu____475 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in (

let uu____477 = (FStar_Options.ml_ish ())
in (match (uu____477) with
| true -> begin
(aux_ml iface impl)
end
| uu____479 -> begin
(aux [] iface impl)
end))))))))))




