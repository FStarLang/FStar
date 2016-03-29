
open Prims
# 24 "FStar.Parser.Interleave.fst"
let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun ds -> (
# 95 "FStar.Parser.Interleave.fst"
let rec head_id_of_pat = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatName (l) -> begin
(l)::[]
end
| FStar_Parser_AST.PatVar (i, _45_9) -> begin
(let _124_5 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_124_5)::[])
end
| FStar_Parser_AST.PatApp (p, _45_14) -> begin
(head_id_of_pat p)
end
| _45_18 -> begin
[]
end))
in (
# 102 "FStar.Parser.Interleave.fst"
let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (
# 104 "FStar.Parser.Interleave.fst"
let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _45_27 -> (match (_45_27) with
| (p, _45_26) -> begin
(head_id_of_pat p)
end)))))
in (
# 106 "FStar.Parser.Interleave.fst"
let prefix_until_let_with_id = (fun ds id -> (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_45_33, _45_35, ps) -> begin
(let _124_18 = (lids_of_let ps)
in (FStar_All.pipe_right _124_18 (FStar_Util.for_some (id_eq_lid id))))
end
| FStar_Parser_AST.Tycon (_45_40, tys) -> begin
if (FStar_All.pipe_right tys (FStar_Util.for_some (fun _45_1 -> (match (_45_1) with
| FStar_Parser_AST.TyconAbbrev (id', _45_47, _45_49, _45_51) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _45_55 -> begin
false
end)))) then begin
(let _124_23 = (let _124_22 = (let _124_21 = (let _124_20 = (FStar_Range.string_of_range id.FStar_Ident.idRange)
in (FStar_Util.format1 "\'type\' abbreviation cannot be given a corresponding \'val\' declaration (%s)" _124_20))
in (_124_21, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_124_22))
in (Prims.raise _124_23))
end else begin
false
end
end
| _45_57 -> begin
false
end)) ds))
in (
# 118 "FStar.Parser.Interleave.fst"
let rec aux = (fun out ds -> (match (ds) with
| [] -> begin
(FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
end
| d::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (qs, x, t) -> begin
(
# 124 "FStar.Parser.Interleave.fst"
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
(let _124_31 = (let _124_30 = (let _124_29 = (let _124_28 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _124_28))
in (_124_29, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_124_30))
in (Prims.raise _124_31))
end else begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_45_78, _45_80, defs) -> begin
(
# 138 "FStar.Parser.Interleave.fst"
let prefix = (d)::prefix
in (
# 139 "FStar.Parser.Interleave.fst"
let def_lids = (lids_of_let defs)
in (
# 140 "FStar.Parser.Interleave.fst"
let popt = (FStar_All.pipe_right prefix (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_45_88, y, _45_91) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _45_95 -> begin
true
end))))
in (
# 147 "FStar.Parser.Interleave.fst"
let _45_137 = (match (popt) with
| None -> begin
((FStar_List.append prefix ((let_x)::[])), suffix)
end
| Some (vals_for_defs, first_non_val_or_unrelated_val, rest) -> begin
(
# 152 "FStar.Parser.Interleave.fst"
let rest = (first_non_val_or_unrelated_val)::rest
in (
# 153 "FStar.Parser.Interleave.fst"
let rec hoist_rest = (fun _45_107 val_ids rest -> (match (_45_107) with
| (hoisted, remaining) -> begin
(match (rest) with
| [] -> begin
((FStar_List.rev hoisted), (FStar_List.rev remaining))
end
| hd::tl -> begin
(match (hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_45_115, x, _45_118) -> begin
(hoist_rest (hoisted, (hd)::remaining) ((x)::val_ids) tl)
end
| FStar_Parser_AST.ToplevelLet (_45_122, _45_124, defs) -> begin
(
# 159 "FStar.Parser.Interleave.fst"
let def_lids = (lids_of_let defs)
in if (FStar_All.pipe_right val_ids (FStar_Util.for_some (fun x -> (FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid x)))))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("The definition is out of order", let_x.FStar_Parser_AST.drange))))
end else begin
(hoist_rest ((hd)::hoisted, remaining) val_ids tl)
end)
end
| _45_131 -> begin
(hoist_rest ((hd)::hoisted, remaining) val_ids tl)
end)
end)
end))
in (
# 167 "FStar.Parser.Interleave.fst"
let _45_134 = (hoist_rest ([], []) [] rest)
in (match (_45_134) with
| (hoisted, remaining) -> begin
((FStar_List.append (FStar_List.append vals_for_defs hoisted) ((let_x)::[])), (FStar_List.append remaining suffix))
end))))
end)
in (match (_45_137) with
| (hoist, suffix) -> begin
(aux ((hoist)::out) suffix)
end)))))
end
| _45_139 -> begin
(FStar_All.failwith "Impossible")
end)
end
end))
end
| FStar_Parser_AST.ToplevelLet (_45_141, _45_143, defs) -> begin
(
# 177 "FStar.Parser.Interleave.fst"
let def_lids = (lids_of_let defs)
in (
# 178 "FStar.Parser.Interleave.fst"
let val_for_defs = (FStar_Util.find_map ds (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_45_150, x, _45_153) when (FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid x))) -> begin
Some ((x, d.FStar_Parser_AST.drange))
end
| _45_157 -> begin
None
end)))
in (match (val_for_defs) with
| Some (x, r) -> begin
(let _124_44 = (let _124_43 = (let _124_42 = (let _124_41 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "Definition of %s precedes its declaration at %s" x.FStar_Ident.idText _124_41))
in (_124_42, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_124_43))
in (Prims.raise _124_44))
end
| None -> begin
(aux (((d)::[])::out) ds)
end)))
end
| _45_165 -> begin
(aux (((d)::[])::out) ds)
end)
end))
in (aux [] ds)))))))

# 190 "FStar.Parser.Interleave.fst"
let interleave_modul : FStar_Parser_AST.modul  ->  FStar_Parser_AST.modul = (fun m -> (match (m) with
| FStar_Parser_AST.Module (l, ds) -> begin
(let _124_48 = (let _124_47 = (interleave ds)
in (l, _124_47))
in FStar_Parser_AST.Module (_124_48))
end
| _45_172 -> begin
m
end))




