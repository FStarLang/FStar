
open Prims

let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface impl -> (

let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (

let is_val = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, _65_13) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _65_17 -> begin
false
end))
in (

let is_type = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_65_22, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun _65_29 -> (match (_65_29) with
| (t, _65_28) -> begin
((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText)
end))))
end
| _65_31 -> begin
false
end))
in (

let is_let = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (_65_36, defs) -> begin
(let _163_22 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right _163_22 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (_65_41, tys) -> begin
(let _163_25 = (FStar_All.pipe_right tys (FStar_List.map (fun _65_48 -> (match (_65_48) with
| (x, _65_47) -> begin
x
end))))
in (FStar_All.pipe_right _163_25 (FStar_Util.for_some (fun _65_1 -> (match (_65_1) with
| FStar_Parser_AST.TyconAbbrev (id', _65_52, _65_54, _65_56) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _65_60 -> begin
false
end)))))
end
| _65_62 -> begin
false
end))
in (

let prefix_until_let = (fun x ds -> (FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))))
in (

let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(let _163_36 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append _163_36 impl))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_65_75, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun _65_2 -> (match (_65_2) with
| (FStar_Parser_AST.TyconAbstract (_65_81), _65_84) -> begin
true
end
| _65_87 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let _65_108 = (match ((FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (_65_102); FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = _65_99; FStar_Parser_AST.quals = _65_97; FStar_Parser_AST.attrs = _65_95}) -> begin
(let _163_42 = (let _163_41 = (let _163_40 = (let _163_39 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" _163_39))
in ((_163_40), (r)))
in FStar_Syntax_Syntax.Error (_163_41))
in (Prims.raise _163_42))
end
| Some (i) -> begin
(let _163_46 = (let _163_45 = (let _163_44 = (let _163_43 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" _163_43))
in ((_163_44), (i.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_163_45))
in (Prims.raise _163_46))
end)
in (match ((prefix_until_let x iface)) with
| Some (_65_111) -> begin
(let _163_49 = (let _163_48 = (let _163_47 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((_163_47), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_163_48))
in (Prims.raise _163_49))
end
| None -> begin
(

let lopt = (prefix_until_let x impl)
in (match (lopt) with
| None -> begin
if (FStar_All.pipe_right d.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(aux (((d)::[])::out) ds impl)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "No definition found for " x.FStar_Ident.idText)), (d.FStar_Parser_AST.drange)))))
end
end
| Some (prefix, let_x, rest_impl) -> begin
if (FStar_All.pipe_right d.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(let _163_53 = (let _163_52 = (let _163_51 = (let _163_50 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _163_50))
in ((_163_51), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_163_52))
in (Prims.raise _163_53))
end else begin
(

let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (x, _65_124) -> begin
(x)::[]
end
| _65_128 -> begin
[]
end))))
in (match ((FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))) with
| Some (d) -> begin
(let _163_61 = (let _163_60 = (let _163_59 = (let _163_58 = (FStar_Parser_AST.decl_to_string d)
in (let _163_57 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" _163_58 _163_57)))
in ((_163_59), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_163_60))
in (Prims.raise _163_61))
end
| _65_135 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (_65_137, defs) -> begin
(

let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (

let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, _65_145) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _65_149 -> begin
true
end))))
in (

let _65_159 = (match (iface_prefix_opt) with
| None -> begin
((iface), ([]))
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
((all_vals_for_defs), ((first_non_val)::rest_iface))
end)
in (match (_65_159) with
| (all_vals_for_defs, rest_iface) -> begin
(

let hoist = (FStar_List.append prefix (FStar_List.append all_vals_for_defs ((let_x)::[])))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| _65_162 -> begin
(failwith "Impossible")
end)
end))
end
end))
end))
end
| _65_164 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in (aux [] iface impl))))))))




