
open Prims

let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface impl -> (

let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (

let is_val = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_63_12, y, _63_15) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _63_19 -> begin
false
end))
in (

let is_type = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_63_24, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun _63_31 -> (match (_63_31) with
| (t, _63_30) -> begin
((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText)
end))))
end
| _63_33 -> begin
false
end))
in (

let is_let = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_63_38, _63_40, defs) -> begin
(let _156_22 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right _156_22 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (_63_45, tys) -> begin
(let _156_25 = (FStar_All.pipe_right tys (FStar_List.map (fun _63_52 -> (match (_63_52) with
| (x, _63_51) -> begin
x
end))))
in (FStar_All.pipe_right _156_25 (FStar_Util.for_some (fun _63_1 -> (match (_63_1) with
| FStar_Parser_AST.TyconAbbrev (id', _63_56, _63_58, _63_60) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _63_64 -> begin
false
end)))))
end
| _63_66 -> begin
false
end))
in (

let prefix_until_let = (fun x ds -> (FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))))
in (

let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(let _156_36 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append _156_36 impl))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_63_79, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun _63_2 -> (match (_63_2) with
| (FStar_Parser_AST.TyconAbstract (_63_85), _63_88) -> begin
true
end
| _63_91 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (qs, x, t) -> begin
(

let _63_109 = (match ((FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (_63_103); FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = _63_100}) -> begin
(let _156_42 = (let _156_41 = (let _156_40 = (let _156_39 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" _156_39))
in ((_156_40), (r)))
in FStar_Syntax_Syntax.Error (_156_41))
in (Prims.raise _156_42))
end
| Some (i) -> begin
(let _156_46 = (let _156_45 = (let _156_44 = (let _156_43 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" _156_43))
in ((_156_44), (i.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_156_45))
in (Prims.raise _156_46))
end)
in (match ((prefix_until_let x iface)) with
| Some (_63_112) -> begin
(let _156_49 = (let _156_48 = (let _156_47 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((_156_47), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_156_48))
in (Prims.raise _156_49))
end
| None -> begin
(

let lopt = (prefix_until_let x impl)
in (match (lopt) with
| None -> begin
if (FStar_All.pipe_right qs (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(aux (((d)::[])::out) ds impl)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "No definition found for " x.FStar_Ident.idText)), (d.FStar_Parser_AST.drange)))))
end
end
| Some (prefix, let_x, rest_impl) -> begin
if (FStar_All.pipe_right qs (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(let _156_53 = (let _156_52 = (let _156_51 = (let _156_50 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _156_50))
in ((_156_51), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_156_52))
in (Prims.raise _156_53))
end else begin
(

let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_63_124, x, _63_127) -> begin
(x)::[]
end
| _63_131 -> begin
[]
end))))
in (match ((FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))) with
| Some (d) -> begin
(let _156_61 = (let _156_60 = (let _156_59 = (let _156_58 = (FStar_Parser_AST.decl_to_string d)
in (let _156_57 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" _156_58 _156_57)))
in ((_156_59), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_156_60))
in (Prims.raise _156_61))
end
| _63_138 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_63_140, _63_142, defs) -> begin
(

let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (

let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_63_149, y, _63_152) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _63_156 -> begin
true
end))))
in (

let _63_166 = (match (iface_prefix_opt) with
| None -> begin
((iface), ([]))
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
((all_vals_for_defs), ((first_non_val)::rest_iface))
end)
in (match (_63_166) with
| (all_vals_for_defs, rest_iface) -> begin
(

let hoist = (FStar_List.append prefix (FStar_List.append all_vals_for_defs ((let_x)::[])))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| _63_169 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end))
end))
end
| _63_171 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in (aux [] iface impl))))))))




