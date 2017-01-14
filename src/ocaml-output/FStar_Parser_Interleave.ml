
open Prims

let interleave : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface impl -> (

let id_eq_lid = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))
in (

let is_val = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, _64_11) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _64_15 -> begin
false
end))
in (

let is_type = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_64_20, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun _64_27 -> (match (_64_27) with
| (t, _64_26) -> begin
((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText)
end))))
end
| _64_29 -> begin
false
end))
in (

let is_let = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (_64_34, defs) -> begin
(let _165_22 = (FStar_Parser_AST.lids_of_let defs)
in (FStar_All.pipe_right _165_22 (FStar_Util.for_some (id_eq_lid x))))
end
| FStar_Parser_AST.Tycon (_64_39, tys) -> begin
(let _165_25 = (FStar_All.pipe_right tys (FStar_List.map (fun _64_46 -> (match (_64_46) with
| (x, _64_45) -> begin
x
end))))
in (FStar_All.pipe_right _165_25 (FStar_Util.for_some (fun uu___363 -> (match (uu___363) with
| FStar_Parser_AST.TyconAbbrev (id', _64_50, _64_52, _64_54) -> begin
(x.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _64_58 -> begin
false
end)))))
end
| _64_60 -> begin
false
end))
in (

let prefix_until_let = (fun x ds -> (FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))))
in (

let aux_ml = (fun iface impl -> (

let rec interleave_vals = (fun vals impl -> (match (vals) with
| [] -> begin
impl
end
| ({FStar_Parser_AST.d = FStar_Parser_AST.Val (x, _64_82); FStar_Parser_AST.drange = _64_79; FStar_Parser_AST.doc = _64_77; FStar_Parser_AST.quals = _64_75; FStar_Parser_AST.attrs = _64_73})::remaining_vals -> begin
(

let d = (FStar_List.hd vals)
in (

let lopt = (prefix_until_let x impl)
in (match (lopt) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "No definition found for " x.FStar_Ident.idText)), (d.FStar_Parser_AST.drange)))))
end
| Some (prefix, let_x, rest_impl) -> begin
(

let impl = (FStar_List.append prefix (FStar_List.append ((d)::(let_x)::[]) rest_impl))
in (interleave_vals remaining_vals impl))
end)))
end
| (_64_98)::remaining_vals -> begin
(interleave_vals remaining_vals impl)
end))
in (interleave_vals iface impl)))
in (

let rec aux = (fun out iface impl -> (match (iface) with
| [] -> begin
(let _165_44 = (FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten)
in (FStar_List.append _165_44 impl))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_64_109, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___364 -> (match (uu___364) with
| (FStar_Parser_AST.TyconAbstract (_64_115), _64_118) -> begin
true
end
| _64_121 -> begin
false
end)))) -> begin
(Prims.raise (FStar_Errors.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let _64_142 = (match ((FStar_All.pipe_right impl (FStar_List.tryFind (fun d -> ((is_val x d) || (is_type x d)))))) with
| None -> begin
()
end
| Some ({FStar_Parser_AST.d = FStar_Parser_AST.Val (_64_136); FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = _64_133; FStar_Parser_AST.quals = _64_131; FStar_Parser_AST.attrs = _64_129}) -> begin
(let _165_50 = (let _165_49 = (let _165_48 = (let _165_47 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s is repeated in the implementation" _165_47))
in ((_165_48), (r)))
in FStar_Errors.Error (_165_49))
in (Prims.raise _165_50))
end
| Some (i) -> begin
(let _165_54 = (let _165_53 = (let _165_52 = (let _165_51 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "%s in the interface is implemented with a \'type\'" _165_51))
in ((_165_52), (i.FStar_Parser_AST.drange)))
in FStar_Errors.Error (_165_53))
in (Prims.raise _165_54))
end)
in (match ((prefix_until_let x iface)) with
| Some (_64_145) -> begin
(let _165_57 = (let _165_56 = (let _165_55 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((_165_55), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (_165_56))
in (Prims.raise _165_57))
end
| None -> begin
(

let lopt = (prefix_until_let x impl)
in (match (lopt) with
| None -> begin
if (FStar_All.pipe_right d.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(aux (((d)::[])::out) ds impl)
end else begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "No definition found for " x.FStar_Ident.idText)), (d.FStar_Parser_AST.drange)))))
end
end
| Some (prefix, let_x, rest_impl) -> begin
if (FStar_All.pipe_right d.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption)) then begin
(let _165_61 = (let _165_60 = (let _165_59 = (let _165_58 = (FStar_Range.string_of_range let_x.FStar_Parser_AST.drange)
in (FStar_Util.format2 "Assumed declaration %s is defined at %s" x.FStar_Ident.idText _165_58))
in ((_165_59), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (_165_60))
in (Prims.raise _165_61))
end else begin
(

let remaining_iface_vals = (FStar_All.pipe_right ds (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (x, _64_158) -> begin
(x)::[]
end
| _64_162 -> begin
[]
end))))
in (match ((FStar_All.pipe_right prefix (FStar_List.tryFind (fun d -> (FStar_All.pipe_right remaining_iface_vals (FStar_Util.for_some (fun x -> (is_let x d)))))))) with
| Some (d) -> begin
(let _165_69 = (let _165_68 = (let _165_67 = (let _165_66 = (FStar_Parser_AST.decl_to_string d)
in (let _165_65 = (FStar_Parser_AST.decl_to_string let_x)
in (FStar_Util.format2 "%s is out of order with %s" _165_66 _165_65)))
in ((_165_67), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (_165_68))
in (Prims.raise _165_69))
end
| _64_169 -> begin
(match (let_x.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (_64_171, defs) -> begin
(

let def_lids = (FStar_Parser_AST.lids_of_let defs)
in (

let iface_prefix_opt = (FStar_All.pipe_right iface (FStar_Util.prefix_until (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, _64_179) -> begin
(not ((FStar_All.pipe_right def_lids (FStar_Util.for_some (id_eq_lid y)))))
end
| _64_183 -> begin
true
end))))
in (

let _64_193 = (match (iface_prefix_opt) with
| None -> begin
((iface), ([]))
end
| Some (all_vals_for_defs, first_non_val, rest_iface) -> begin
((all_vals_for_defs), ((first_non_val)::rest_iface))
end)
in (match (_64_193) with
| (all_vals_for_defs, rest_iface) -> begin
(

let hoist = (FStar_List.append prefix (FStar_List.append all_vals_for_defs ((let_x)::[])))
in (aux ((hoist)::out) rest_iface rest_impl))
end))))
end
| _64_196 -> begin
(failwith "Impossible")
end)
end))
end
end))
end))
end
| _64_198 -> begin
(aux (((d)::[])::out) ds impl)
end)
end))
in if (FStar_Options.ml_ish ()) then begin
(aux_ml iface impl)
end else begin
(aux [] iface impl)
end))))))))




