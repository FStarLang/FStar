
open Prims

let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun ds -> (

let rec head_id_of_pat = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatName (l) -> begin
(l)::[]
end
| FStar_Parser_AST.PatVar (i, _55_9) -> begin
(let _144_5 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_144_5)::[])
end
| FStar_Parser_AST.PatApp (p, _55_14) -> begin
(head_id_of_pat p)
end
| FStar_Parser_AST.PatAscribed (p, _55_19) -> begin
(head_id_of_pat p)
end
| _55_23 -> begin
[]
end))
in (

let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (

let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _55_32 -> (match (_55_32) with
| (p, _55_31) -> begin
(head_id_of_pat p)
end)))))
in (

let prefix_until_let_with_id = (fun ds id -> (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_55_38, _55_40, ps) -> begin
(let _144_18 = (lids_of_let ps)
in (FStar_All.pipe_right _144_18 (FStar_Util.for_some (id_eq_lid id))))
end
| FStar_Parser_AST.Tycon (_55_45, tys) -> begin
if (FStar_All.pipe_right tys (FStar_Util.for_some (fun _55_1 -> (match (_55_1) with
| FStar_Parser_AST.TyconAbbrev (id', _55_52, _55_54, _55_56) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _55_60 -> begin
false
end)))) then begin
(let _144_23 = (let _144_22 = (let _144_21 = (let _144_20 = (FStar_Range.string_of_range id.FStar_Ident.idRange)
in (FStar_Util.format1 "\'type\' abbreviation cannot be given a corresponding \'val\' declaration (%s)" _144_20))
in (_144_21, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_144_22))
in (Prims.raise _144_23))
end else begin
false
end
end
| _55_62 -> begin
false
end)) ds))
in (

let rec aux = (fun out ds -> (match (ds) with
| [] -> begin
(FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
end
| d::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (qs, x, t) -> begin
(

let lopt = (prefix_until_let_with_id ds x)
in (match (lopt) with
| None -> begin
if (FStar_All.pipe_right qs (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(aux (((d)::[])::out) ds)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "No definition found for " x.FStar_Ident.idText), d.FStar_Parser_AST.drange))))
end
end
| Some (prefix, let_x, suffix) -> begin
if (FStar_All.pipe_right qs (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(let _144_31 = (let _144_30 = (let _144_29 = (let _144_28 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _144_28))
in (_144_29, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_144_30))
in (Prims.raise _144_31))
end else begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_55_83, _55_85, defs) -> begin
(

let prefix = (d)::prefix
in (

let def_lids = (lids_of_let defs)
in (

let popt = (FStar_All.pipe_right prefix (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_55_93, y, _55_96) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _55_100 -> begin
true
end))))
in (

let _55_142 = (match (popt) with
| None -> begin
((FStar_List.append prefix ((let_x)::[])), suffix)
end
| Some (vals_for_defs, first_non_val_or_unrelated_val, rest) -> begin
(

let rest = (first_non_val_or_unrelated_val)::rest
in (

let rec hoist_rest = (fun _55_112 val_ids rest -> (match (_55_112) with
| (hoisted, remaining) -> begin
(match (rest) with
| [] -> begin
((FStar_List.rev hoisted), (FStar_List.rev remaining))
end
| hd::tl -> begin
(match (hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_55_120, x, _55_123) -> begin
(hoist_rest (hoisted, (hd)::remaining) ((x)::val_ids) tl)
end
| FStar_Parser_AST.ToplevelLet (_55_127, _55_129, defs) -> begin
(

let def_lids' = (lids_of_let defs)
in if (FStar_All.pipe_right val_ids (FStar_Util.for_some (fun x -> (FStar_All.pipe_right def_lids' (FStar_Util.for_some (id_eq_lid x)))))) then begin
(let _144_46 = (let _144_45 = (let _144_44 = (let _144_43 = (let _144_40 = (FStar_All.pipe_right def_lids FStar_List.hd)
in (FStar_All.pipe_right _144_40 FStar_Syntax_Print.lid_to_string))
in (let _144_42 = (let _144_41 = (FStar_All.pipe_right def_lids' FStar_List.hd)
in (FStar_All.pipe_right _144_41 FStar_Syntax_Print.lid_to_string))
in (FStar_Util.format2 "The definition for \'%s\' is out of order with \'%s\'" _144_43 _144_42)))
in (_144_44, let_x.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_144_45))
in (Prims.raise _144_46))
end else begin
(hoist_rest ((hd)::hoisted, remaining) val_ids tl)
end)
end
| _55_136 -> begin
(hoist_rest ((hd)::hoisted, remaining) val_ids tl)
end)
end)
end))
in (

let _55_139 = (hoist_rest ([], []) [] rest)
in (match (_55_139) with
| (hoisted, remaining) -> begin
((FStar_List.append (FStar_List.append vals_for_defs hoisted) ((let_x)::[])), (FStar_List.append remaining suffix))
end))))
end)
in (match (_55_142) with
| (hoist, suffix) -> begin
(aux ((hoist)::out) suffix)
end)))))
end
| _55_144 -> begin
(FStar_All.failwith "Impossible")
end)
end
end))
end
| FStar_Parser_AST.ToplevelLet (_55_146, _55_148, defs) -> begin
(

let def_lids = (lids_of_let defs)
in (

let val_for_defs = (FStar_Util.find_map ds (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_55_155, x, _55_158) when (FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid x))) -> begin
Some ((x, d.FStar_Parser_AST.drange))
end
| _55_162 -> begin
None
end)))
in (match (val_for_defs) with
| Some (x, r) -> begin
(let _144_51 = (let _144_50 = (let _144_49 = (let _144_48 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "Definition of %s precedes its declaration at %s" x.FStar_Ident.idText _144_48))
in (_144_49, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_144_50))
in (Prims.raise _144_51))
end
| None -> begin
(aux (((d)::[])::out) ds)
end)))
end
| _55_170 -> begin
(aux (((d)::[])::out) ds)
end)
end))
in (aux [] ds)))))))


let interleave_modul : FStar_Parser_AST.modul  ->  FStar_Parser_AST.modul = (fun m -> (match (m) with
| FStar_Parser_AST.Module (l, ds) -> begin
(let _144_55 = (let _144_54 = (interleave ds)
in (l, _144_54))
in FStar_Parser_AST.Module (_144_55))
end
| _55_177 -> begin
m
end))




