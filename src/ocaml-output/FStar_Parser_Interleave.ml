
open Prims

let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface impl -> (

let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (

let is_val = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_64_12, y, _64_15) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _64_19 -> begin
false
end))
in (

let is_type = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_64_24, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun _64_31 -> (match (_64_31) with
| (t, _64_30) -> begin
((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText)
end))))
end
| _64_33 -> begin
false
end))
in (

let is_let = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_64_38, _64_40, defs) -> begin
(let _161_22 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right _161_22 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (_64_45, tys) -> begin
(let _161_25 = (FStar_All.pipe_right tys (FStar_List.map (fun _64_52 -> (match (_64_52) with
| (x, _64_51) -> begin
x
end))))
in (FStar_All.pipe_right _161_25 (FStar_Util.for_some (fun _64_1 -> (match (_64_1) with
| FStar_Parser_AST.TyconAbbrev (id', _64_56, _64_58, _64_60) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _64_64 -> begin
false
end)))))
end
| _64_66 -> begin
false
end))
in (

let prefix_until_let = (fun x ds -> (FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))))
in (

let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(let _161_36 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append _161_36 impl))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_64_79, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun _64_2 -> (match (_64_2) with
| (FStar_Parser_AST.TyconAbstract (_64_85), _64_88) -> begin
true
end
| _64_91 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (qs, x, t) -> begin
(

let _64_109 = (match ((FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (_64_103); FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = _64_100}) -> begin
(let _161_42 = (let _161_41 = (let _161_40 = (let _161_39 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" _161_39))
in ((_161_40), (r)))
in FStar_Syntax_Syntax.Error (_161_41))
in (Prims.raise _161_42))
end
| Some (i) -> begin
(let _161_46 = (let _161_45 = (let _161_44 = (let _161_43 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" _161_43))
in ((_161_44), (i.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_161_45))
in (Prims.raise _161_46))
end)
in (match ((prefix_until_let x iface)) with
| Some (_64_112) -> begin
(let _161_49 = (let _161_48 = (let _161_47 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((_161_47), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_161_48))
in (Prims.raise _161_49))
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
(let _161_53 = (let _161_52 = (let _161_51 = (let _161_50 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _161_50))
in ((_161_51), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_161_52))
in (Prims.raise _161_53))
end else begin
(

let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_64_124, x, _64_127) -> begin
(x)::[]
end
| _64_131 -> begin
[]
end))))
in (match ((FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))) with
| Some (d) -> begin
(let _161_61 = (let _161_60 = (let _161_59 = (let _161_58 = (FStar_Parser_AST.decl_to_string d)
in (let _161_57 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" _161_58 _161_57)))
in ((_161_59), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_161_60))
in (Prims.raise _161_61))
end
| _64_138 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_64_140, _64_142, defs) -> begin
(

let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (

let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_64_149, y, _64_152) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _64_156 -> begin
true
end))))
in (

let _64_166 = (match (iface_prefix_opt) with
| None -> begin
((iface), ([]))
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
((all_vals_for_defs), ((first_non_val)::rest_iface))
end)
in (match (_64_166) with
| (all_vals_for_defs, rest_iface) -> begin
(

let hoist = (FStar_List.append prefix (FStar_List.append all_vals_for_defs ((let_x)::[])))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| _64_169 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end))
end))
end
| _64_171 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in (aux [] iface impl))))))))




