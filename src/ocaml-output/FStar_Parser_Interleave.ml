
open Prims
# 94 "FStar.Parser.Interleave.fst"
let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun ds -> (
# 95 "FStar.Parser.Interleave.fst"
let rec head_id_of_pat = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatName (l) -> begin
(l)::[]
end
| FStar_Parser_AST.PatVar (i, _51_9) -> begin
(let _136_5 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_136_5)::[])
end
| FStar_Parser_AST.PatApp (p, _51_14) -> begin
(head_id_of_pat p)
end
| _51_18 -> begin
[]
end))
in (
# 102 "FStar.Parser.Interleave.fst"
let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (
# 104 "FStar.Parser.Interleave.fst"
let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _51_27 -> (match (_51_27) with
| (p, _51_26) -> begin
(head_id_of_pat p)
end)))))
in (
# 106 "FStar.Parser.Interleave.fst"
let prefix_until_let_with_id = (fun ds id -> (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_51_33, _51_35, ps) -> begin
(let _136_18 = (lids_of_let ps)
in (FStar_All.pipe_right _136_18 (FStar_Util.for_some (id_eq_lid id))))
end
| FStar_Parser_AST.Tycon (_51_40, tys) -> begin
if (FStar_All.pipe_right tys (FStar_Util.for_some (fun _51_1 -> (match (_51_1) with
| FStar_Parser_AST.TyconAbbrev (id', _51_47, _51_49, _51_51) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _51_55 -> begin
false
end)))) then begin
(let _136_23 = (let _136_22 = (let _136_21 = (let _136_20 = (FStar_Range.string_of_range id.FStar_Ident.idRange)
in (FStar_Util.format1 "\'type\' abbreviation cannot be given a corresponding \'val\' declaration (%s)" _136_20))
in (_136_21, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_136_22))
in (Prims.raise _136_23))
end else begin
false
end
end
| _51_57 -> begin
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
(let _136_31 = (let _136_30 = (let _136_29 = (let _136_28 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _136_28))
in (_136_29, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_136_30))
in (Prims.raise _136_31))
end else begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_51_78, _51_80, defs) -> begin
(
# 138 "FStar.Parser.Interleave.fst"
let prefix = (d)::prefix
in (
# 139 "FStar.Parser.Interleave.fst"
let def_lids = (lids_of_let defs)
in (
# 140 "FStar.Parser.Interleave.fst"
let popt = (FStar_All.pipe_right prefix (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_51_88, y, _51_91) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _51_95 -> begin
true
end))))
in (
# 147 "FStar.Parser.Interleave.fst"
let _51_137 = (match (popt) with
| None -> begin
((FStar_List.append prefix ((let_x)::[])), suffix)
end
| Some (vals_for_defs, first_non_val_or_unrelated_val, rest) -> begin
(
# 152 "FStar.Parser.Interleave.fst"
let rest = (first_non_val_or_unrelated_val)::rest
in (
# 153 "FStar.Parser.Interleave.fst"
let rec hoist_rest = (fun _51_107 val_ids rest -> (match (_51_107) with
| (hoisted, remaining) -> begin
(match (rest) with
| [] -> begin
((FStar_List.rev hoisted), (FStar_List.rev remaining))
end
| hd::tl -> begin
(match (hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_51_115, x, _51_118) -> begin
(hoist_rest (hoisted, (hd)::remaining) ((x)::val_ids) tl)
end
| FStar_Parser_AST.ToplevelLet (_51_122, _51_124, defs) -> begin
(
# 159 "FStar.Parser.Interleave.fst"
let def_lids = (lids_of_let defs)
in if (FStar_All.pipe_right val_ids (FStar_Util.for_some (fun x -> (FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid x)))))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("The definition at %s is out of order", let_x.FStar_Parser_AST.drange))))
end else begin
(hoist_rest ((hd)::hoisted, remaining) val_ids tl)
end)
end
| _51_131 -> begin
(hoist_rest ((hd)::hoisted, remaining) val_ids tl)
end)
end)
end))
in (
# 167 "FStar.Parser.Interleave.fst"
let _51_134 = (hoist_rest ([], []) [] rest)
in (match (_51_134) with
| (hoisted, remaining) -> begin
((FStar_List.append (FStar_List.append vals_for_defs hoisted) ((let_x)::[])), (FStar_List.append remaining suffix))
end))))
end)
in (match (_51_137) with
| (hoist, suffix) -> begin
(aux ((hoist)::out) suffix)
end)))))
end
| _51_139 -> begin
(FStar_All.failwith "Impossible")
end)
end
end))
end
| FStar_Parser_AST.ToplevelLet (_51_141, _51_143, defs) -> begin
(
# 177 "FStar.Parser.Interleave.fst"
let def_lids = (lids_of_let defs)
in (
# 178 "FStar.Parser.Interleave.fst"
let val_for_defs = (FStar_Util.find_map ds (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_51_150, x, _51_153) when (FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid x))) -> begin
Some ((x, d.FStar_Parser_AST.drange))
end
| _51_157 -> begin
None
end)))
in (match (val_for_defs) with
| Some (x, r) -> begin
(let _136_44 = (let _136_43 = (let _136_42 = (let _136_41 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "Definition of %s precedes its declaration at %s" x.FStar_Ident.idText _136_41))
in (_136_42, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_136_43))
in (Prims.raise _136_44))
end
| None -> begin
(aux (((d)::[])::out) ds)
end)))
end
| _51_165 -> begin
(aux (((d)::[])::out) ds)
end)
end))
in (aux [] ds)))))))

# 192 "FStar.Parser.Interleave.fst"
let interleave_modul : FStar_Parser_AST.modul  ->  FStar_Parser_AST.modul = (fun m -> if (FStar_ST.read FStar_Options.interleave) then begin
(match (m) with
| FStar_Parser_AST.Module (l, ds) -> begin
(let _136_48 = (let _136_47 = (interleave ds)
in (l, _136_47))
in FStar_Parser_AST.Module (_136_48))
end
| _51_172 -> begin
m
end)
end else begin
m
end)




