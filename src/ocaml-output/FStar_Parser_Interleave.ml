
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
(FStar_All.pipe_right tys (FStar_Util.for_some (fun t -> ((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))))
end
| _63_30 -> begin
false
end))
in (

let is_let = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_63_35, _63_37, defs) -> begin
(let _155_22 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right _155_22 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (_63_42, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun _63_1 -> (match (_63_1) with
| FStar_Parser_AST.TyconAbbrev (id', _63_49, _63_51, _63_53) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _63_57 -> begin
false
end))))
end
| _63_59 -> begin
false
end))
in (

let prefix_until_let = (fun x ds -> (FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))))
in (

let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(let _155_34 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append _155_34 impl))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_63_72, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun _63_2 -> (match (_63_2) with
| FStar_Parser_AST.TyconAbstract (_63_78) -> begin
true
end
| _63_81 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (qs, x, t) -> begin
(

let _63_97 = (match ((FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (_63_91); FStar_Parser_AST.drange = r}) -> begin
(let _155_40 = (let _155_39 = (let _155_38 = (let _155_37 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" _155_37))
in ((_155_38), (r)))
in FStar_Syntax_Syntax.Error (_155_39))
in (Prims.raise _155_40))
end
| Some (i) -> begin
(let _155_44 = (let _155_43 = (let _155_42 = (let _155_41 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" _155_41))
in ((_155_42), (i.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_155_43))
in (Prims.raise _155_44))
end)
in (match ((prefix_until_let x iface)) with
| Some (_63_100) -> begin
(let _155_47 = (let _155_46 = (let _155_45 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((_155_45), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_155_46))
in (Prims.raise _155_47))
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
(let _155_51 = (let _155_50 = (let _155_49 = (let _155_48 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _155_48))
in ((_155_49), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_155_50))
in (Prims.raise _155_51))
end else begin
(

let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_63_112, x, _63_115) -> begin
(x)::[]
end
| _63_119 -> begin
[]
end))))
in (match ((FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))) with
| Some (d) -> begin
(let _155_59 = (let _155_58 = (let _155_57 = (let _155_56 = (FStar_Parser_AST.decl_to_string d)
in (let _155_55 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" _155_56 _155_55)))
in ((_155_57), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_155_58))
in (Prims.raise _155_59))
end
| _63_126 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_63_128, _63_130, defs) -> begin
(

let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (

let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_63_137, y, _63_140) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _63_144 -> begin
true
end))))
in (

let _63_154 = (match (iface_prefix_opt) with
| None -> begin
((iface), ([]))
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
((all_vals_for_defs), ((first_non_val)::rest_iface))
end)
in (match (_63_154) with
| (all_vals_for_defs, rest_iface) -> begin
(

let hoist = (FStar_List.append prefix (FStar_List.append all_vals_for_defs ((let_x)::[])))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| _63_157 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end))
end))
end
| _63_159 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in (aux [] iface impl))))))))




