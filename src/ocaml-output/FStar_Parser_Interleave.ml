
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
(let _0_857 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right _0_857 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (uu____79, tys) -> begin
(let _0_858 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____98 -> (match (uu____98) with
| (x, uu____103) -> begin
x
end))))
in (FStar_All.pipe_right _0_858 (FStar_Util.for_some (fun uu___143_106 -> (match (uu___143_106) with
| FStar_Parser_AST.TyconAbbrev (id', uu____108, uu____109, uu____110) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| uu____115 -> begin
false
end)))))
end
| uu____116 -> begin
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
| ({FStar_Parser_AST.d = FStar_Parser_AST.Val (x, uu____166); FStar_Parser_AST.drange = uu____167; FStar_Parser_AST.doc = uu____168; FStar_Parser_AST.quals = uu____169; FStar_Parser_AST.attrs = uu____170})::remaining_vals -> begin
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
| (uu____203)::remaining_vals -> begin
(interleave_vals remaining_vals impl)
end))
in (interleave_vals iface impl)))
in (

let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(let _0_859 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append _0_859 impl))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____234, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___144_251 -> (match (uu___144_251) with
| (FStar_Parser_AST.TyconAbstract (uu____255), uu____256) -> begin
true
end
| uu____264 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Errors.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
((

let uu____272 = (FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))
in (match (uu____272) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (uu____277); FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = uu____279; FStar_Parser_AST.quals = uu____280; FStar_Parser_AST.attrs = uu____281}) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_861 = (let _0_860 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" _0_860))
in ((_0_861), (r))))))
end
| Some (i) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_863 = (let _0_862 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" _0_862))
in ((_0_863), (i.FStar_Parser_AST.drange))))))
end));
(

let uu____286 = (prefix_until_let x iface)
in (match (uu____286) with
| Some (uu____294) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_864 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((_0_864), (d.FStar_Parser_AST.drange))))))
end
| None -> begin
(

let lopt = (prefix_until_let x impl)
in (match (lopt) with
| None -> begin
(

let uu____324 = (FStar_All.pipe_right d.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____324) with
| true -> begin
(aux (((d)::[])::out) ds impl)
end
| uu____327 -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "No definition found for " x.FStar_Ident.idText)), (d.FStar_Parser_AST.drange)))))
end))
end
| Some (prefix, let_x, rest_impl) -> begin
(

let uu____341 = (FStar_All.pipe_right d.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____341) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_866 = (let _0_865 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _0_865))
in ((_0_866), (d.FStar_Parser_AST.drange))))))
end
| uu____344 -> begin
(

let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (x, uu____352) -> begin
(x)::[]
end
| uu____353 -> begin
[]
end))))
in (

let uu____354 = (FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))
in (match (uu____354) with
| Some (d) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_869 = (let _0_868 = (FStar_Parser_AST.decl_to_string d)
in (let _0_867 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" _0_868 _0_867)))
in ((_0_869), (d.FStar_Parser_AST.drange))))))
end
| uu____364 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____367, defs) -> begin
(

let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (

let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, uu____393) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| uu____395 -> begin
true
end))))
in (

let uu____396 = (match (iface_prefix_opt) with
| None -> begin
((iface), ([]))
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
((all_vals_for_defs), ((first_non_val)::rest_iface))
end)
in (match (uu____396) with
| (all_vals_for_defs, rest_iface) -> begin
(

let hoist = (FStar_List.append prefix (FStar_List.append all_vals_for_defs ((let_x)::[])))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| uu____436 -> begin
(failwith "Impossible")
end)
end)))
end))
end))
end));
)
end
| uu____438 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in (

let uu____440 = (FStar_Options.ml_ish ())
in (match (uu____440) with
| true -> begin
(aux_ml iface impl)
end
| uu____442 -> begin
(aux [] iface impl)
end))))))))))




