
open Prims
# 94 "FStar.Parser.Interleave.fst"
let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface impl -> (
# 95 "FStar.Parser.Interleave.fst"
let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (
# 97 "FStar.Parser.Interleave.fst"
let is_val = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_55_12, y, _55_15) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _55_19 -> begin
false
end))
in (
# 101 "FStar.Parser.Interleave.fst"
let is_type = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_55_24, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun t -> ((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))))
end
| _55_30 -> begin
false
end))
in (
# 107 "FStar.Parser.Interleave.fst"
let is_let = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_55_35, _55_37, defs) -> begin
(let _144_22 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right _144_22 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (_55_42, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun _55_1 -> (match (_55_1) with
| FStar_Parser_AST.TyconAbbrev (id', _55_49, _55_51, _55_53) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _55_57 -> begin
false
end))))
end
| _55_59 -> begin
false
end))
in (
# 117 "FStar.Parser.Interleave.fst"
let prefix_until_let = (fun x ds -> (FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))))
in (
# 119 "FStar.Parser.Interleave.fst"
let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(let _144_34 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append _144_34 impl))
end
| d::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_55_72, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun _55_2 -> (match (_55_2) with
| FStar_Parser_AST.TyconAbstract (_55_78) -> begin
true
end
| _55_81 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Interface contains an abstract \'type\' declaration; use \'val\' instead", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Val (qs, x, t) -> begin
(
# 128 "FStar.Parser.Interleave.fst"
let _55_97 = (match ((FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (_55_91); FStar_Parser_AST.drange = r}) -> begin
(let _144_40 = (let _144_39 = (let _144_38 = (let _144_37 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" _144_37))
in (_144_38, r))
in FStar_Syntax_Syntax.Error (_144_39))
in (Prims.raise _144_40))
end
| Some (i) -> begin
(let _144_44 = (let _144_43 = (let _144_42 = (let _144_41 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" _144_41))
in (_144_42, i.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_144_43))
in (Prims.raise _144_44))
end)
in (match ((prefix_until_let x iface)) with
| Some (_55_100) -> begin
(let _144_47 = (let _144_46 = (let _144_45 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in (_144_45, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_144_46))
in (Prims.raise _144_47))
end
| None -> begin
(
# 135 "FStar.Parser.Interleave.fst"
let lopt = (prefix_until_let x impl)
in (match (lopt) with
| None -> begin
if (FStar_All.pipe_right qs (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(aux (((d)::[])::out) ds impl)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "No definition found for " x.FStar_Ident.idText), d.FStar_Parser_AST.drange))))
end
end
| Some (prefix, let_x, rest_impl) -> begin
if (FStar_All.pipe_right qs (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(let _144_51 = (let _144_50 = (let _144_49 = (let _144_48 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _144_48))
in (_144_49, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_144_50))
in (Prims.raise _144_51))
end else begin
(
# 147 "FStar.Parser.Interleave.fst"
let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_55_112, x, _55_115) -> begin
(x)::[]
end
| _55_119 -> begin
[]
end))))
in (match ((FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))) with
| Some (d) -> begin
(let _144_59 = (let _144_58 = (let _144_57 = (let _144_56 = (FStar_Parser_AST.decl_to_string d)
in (let _144_55 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" _144_56 _144_55)))
in (_144_57, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_144_58))
in (Prims.raise _144_59))
end
| _55_126 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.ToplevelLet (_55_128, _55_130, defs) -> begin
(
# 156 "FStar.Parser.Interleave.fst"
let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (
# 157 "FStar.Parser.Interleave.fst"
let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (_55_137, y, _55_140) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _55_144 -> begin
true
end))))
in (
# 163 "FStar.Parser.Interleave.fst"
let _55_154 = (match (iface_prefix_opt) with
| None -> begin
(iface, [])
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
(all_vals_for_defs, (first_non_val)::rest_iface)
end)
in (match (_55_154) with
| (all_vals_for_defs, rest_iface) -> begin
(
# 170 "FStar.Parser.Interleave.fst"
let hoist = (FStar_List.append (FStar_List.append prefix all_vals_for_defs) ((let_x)::[]))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| _55_157 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end))
end))
end
| _55_159 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in (
# 180 "FStar.Parser.Interleave.fst"
let decls = (aux [] iface impl)
in (
# 181 "FStar.Parser.Interleave.fst"
let _55_161 = if (let _144_61 = (FStar_ST.read FStar_Options.debug_level)
in (FStar_All.pipe_right _144_61 (FStar_List.contains (FStar_Options.Other ("Interleaving"))))) then begin
(let _144_63 = (let _144_62 = (FStar_List.map FStar_Parser_AST.decl_to_string decls)
in (FStar_All.pipe_right _144_62 (FStar_String.concat "\n")))
in (FStar_Util.print_string _144_63))
end else begin
()
end
in decls)))))))))




