
open Prims
# 94 "FStar.Parser.Interleave.fst"
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
| FStar_Parser_AST.PatAscribed (p, _45_19) -> begin
(head_id_of_pat p)
end
| _45_23 -> begin
[]
end))
in (
# 103 "FStar.Parser.Interleave.fst"
let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (
# 105 "FStar.Parser.Interleave.fst"
let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _45_32 -> (match (_45_32) with
| (p, _45_31) -> begin
(head_id_of_pat p)
end)))))
in (
# 107 "FStar.Parser.Interleave.fst"
let prefix_until_let_with_id = (fun ds id -> (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_45_38, _45_40, ps) -> begin
(let _124_18 = (lids_of_let ps)
in (FStar_All.pipe_right _124_18 (FStar_Util.for_some (id_eq_lid id))))
end
| FStar_Parser_AST.Tycon (_45_45, tys) -> begin
if (FStar_All.pipe_right tys (FStar_Util.for_some (fun _45_1 -> (match (_45_1) with
| FStar_Parser_AST.TyconAbbrev (id', _45_52, _45_54, _45_56) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _45_60 -> begin
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
| _45_62 -> begin
false
end)) ds))
in (
# 119 "FStar.Parser.Interleave.fst"
let rec aux = (fun out ds -> (match (ds) with
| [] -> begin
(FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
end
| d::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (qs, x, t) -> begin
(
# 125 "FStar.Parser.Interleave.fst"
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
| FStar_Parser_AST.ToplevelLet (_45_83, _45_85, defs) -> begin
(
# 139 "FStar.Parser.Interleave.fst"
let prefix = (d)::prefix
in (
# 140 "FStar.Parser.Interleave.fst"
let def_lids = (lids_of_let defs)
in (
# 141 "FStar.Parser.Interleave.fst"
let popt = (FStar_All.pipe_right prefix (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_45_93, y, _45_96) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _45_100 -> begin
true
end))))
in (
# 148 "FStar.Parser.Interleave.fst"
let _45_142 = (match (popt) with
| None -> begin
((FStar_List.append prefix ((let_x)::[])), suffix)
end
| Some (vals_for_defs, first_non_val_or_unrelated_val, rest) -> begin
(
# 153 "FStar.Parser.Interleave.fst"
let rest = (first_non_val_or_unrelated_val)::rest
in (
# 154 "FStar.Parser.Interleave.fst"
let rec hoist_rest = (fun _45_112 val_ids rest -> (match (_45_112) with
| (hoisted, remaining) -> begin
(match (rest) with
| [] -> begin
((FStar_List.rev hoisted), (FStar_List.rev remaining))
end
| hd::tl -> begin
(match (hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_45_120, x, _45_123) -> begin
(hoist_rest (hoisted, (hd)::remaining) ((x)::val_ids) tl)
end
| FStar_Parser_AST.ToplevelLet (_45_127, _45_129, defs) -> begin
(
# 160 "FStar.Parser.Interleave.fst"
let def_lids' = (lids_of_let defs)
in if (FStar_All.pipe_right val_ids (FStar_Util.for_some (fun x -> (FStar_All.pipe_right def_lids' (FStar_Util.for_some (id_eq_lid x)))))) then begin
(let _124_46 = (let _124_45 = (let _124_44 = (let _124_43 = (let _124_40 = (FStar_All.pipe_right def_lids FStar_List.hd)
in (FStar_All.pipe_right _124_40 FStar_Syntax_Print.lid_to_string))
in (let _124_42 = (let _124_41 = (FStar_All.pipe_right def_lids' FStar_List.hd)
in (FStar_All.pipe_right _124_41 FStar_Syntax_Print.lid_to_string))
in (FStar_Util.format2 "The definition for \'%s\' is out of order with \'%s\'" _124_43 _124_42)))
in (_124_44, let_x.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_124_45))
in (Prims.raise _124_46))
end else begin
(hoist_rest ((hd)::hoisted, remaining) val_ids tl)
end)
end
| _45_136 -> begin
(hoist_rest ((hd)::hoisted, remaining) val_ids tl)
end)
end)
end))
in (
# 171 "FStar.Parser.Interleave.fst"
let _45_139 = (hoist_rest ([], []) [] rest)
in (match (_45_139) with
| (hoisted, remaining) -> begin
((FStar_List.append (FStar_List.append vals_for_defs hoisted) ((let_x)::[])), (FStar_List.append remaining suffix))
end))))
end)
in (match (_45_142) with
| (hoist, suffix) -> begin
(aux ((hoist)::out) suffix)
end)))))
end
| _45_144 -> begin
(FStar_All.failwith "Impossible")
end)
end
end))
end
| FStar_Parser_AST.ToplevelLet (_45_146, _45_148, defs) -> begin
(
# 181 "FStar.Parser.Interleave.fst"
let def_lids = (lids_of_let defs)
in (
# 182 "FStar.Parser.Interleave.fst"
let val_for_defs = (FStar_Util.find_map ds (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_45_155, x, _45_158) when (FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid x))) -> begin
Some ((x, d.FStar_Parser_AST.drange))
end
| _45_162 -> begin
None
end)))
in (match (val_for_defs) with
| Some (x, r) -> begin
(let _124_51 = (let _124_50 = (let _124_49 = (let _124_48 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "Definition of %s precedes its declaration at %s" x.FStar_Ident.idText _124_48))
in (_124_49, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_124_50))
in (Prims.raise _124_51))
end
| None -> begin
(aux (((d)::[])::out) ds)
end)))
end
| _45_170 -> begin
(aux (((d)::[])::out) ds)
end)
end))
in (aux [] ds)))))))

# 196 "FStar.Parser.Interleave.fst"
let interleave_modul : FStar_Parser_AST.modul  ->  FStar_Parser_AST.modul = (fun m -> (match (m) with
| FStar_Parser_AST.Module (l, ds) -> begin
(let _124_55 = (let _124_54 = (interleave ds)
in (l, _124_54))
in FStar_Parser_AST.Module (_124_55))
end
| _45_177 -> begin
m
end))




