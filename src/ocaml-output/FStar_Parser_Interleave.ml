
open Prims

let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface impl -> (

let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (

let is_val = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, _66_13) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _66_17 -> begin
false
end))
in (

let is_type = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_66_22, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun _66_29 -> (match (_66_29) with
| (t, _66_28) -> begin
((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText)
end))))
end
| _66_31 -> begin
false
end))
in (

let is_let = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (_66_36, defs) -> begin
(let _164_22 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right _164_22 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (_66_41, tys) -> begin
(let _164_25 = (FStar_All.pipe_right tys (FStar_List.map (fun _66_48 -> (match (_66_48) with
| (x, _66_47) -> begin
x
end))))
in (FStar_All.pipe_right _164_25 (FStar_Util.for_some (fun _66_1 -> (match (_66_1) with
| FStar_Parser_AST.TyconAbbrev (id', _66_52, _66_54, _66_56) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _66_60 -> begin
false
end)))))
end
| _66_62 -> begin
false
end))
in (

let prefix_until_let = (fun x ds -> (FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))))
in (

let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(let _164_36 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append _164_36 impl))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_66_75, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun _66_2 -> (match (_66_2) with
| (FStar_Parser_AST.TyconAbstract (_66_81), _66_84) -> begin
true
end
| _66_87 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let _66_108 = (match ((FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (_66_102); FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = _66_99; FStar_Parser_AST.quals = _66_97; FStar_Parser_AST.attrs = _66_95}) -> begin
(let _164_42 = (let _164_41 = (let _164_40 = (let _164_39 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" _164_39))
in ((_164_40), (r)))
in FStar_Syntax_Syntax.Error (_164_41))
in (Prims.raise _164_42))
end
| Some (i) -> begin
(let _164_46 = (let _164_45 = (let _164_44 = (let _164_43 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" _164_43))
in ((_164_44), (i.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_164_45))
in (Prims.raise _164_46))
end)
in (match ((prefix_until_let x iface)) with
| Some (_66_111) -> begin
(let _164_49 = (let _164_48 = (let _164_47 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((_164_47), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_164_48))
in (Prims.raise _164_49))
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
(let _164_53 = (let _164_52 = (let _164_51 = (let _164_50 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _164_50))
in ((_164_51), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_164_52))
in (Prims.raise _164_53))
end else begin
(

let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (x, _66_124) -> begin
(x)::[]
end
| _66_128 -> begin
[]
end))))
in (match ((FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))) with
| Some (d) -> begin
(let _164_61 = (let _164_60 = (let _164_59 = (let _164_58 = (FStar_Parser_AST.decl_to_string d)
in (let _164_57 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" _164_58 _164_57)))
in ((_164_59), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_164_60))
in (Prims.raise _164_61))
end
| _66_135 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (_66_137, defs) -> begin
(

let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (

let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, _66_145) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _66_149 -> begin
true
end))))
in (

let _66_159 = (match (iface_prefix_opt) with
| None -> begin
((iface), ([]))
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
((all_vals_for_defs), ((first_non_val)::rest_iface))
end)
in (match (_66_159) with
| (all_vals_for_defs, rest_iface) -> begin
(

let hoist = (FStar_List.append prefix (FStar_List.append all_vals_for_defs ((let_x)::[])))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| _66_162 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end))
end))
end
| _66_164 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in (aux [] iface impl))))))))




