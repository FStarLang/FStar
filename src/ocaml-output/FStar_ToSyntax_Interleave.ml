
open Prims
open FStar_Pervasives

let id_eq_lid : FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.bool = (fun i l -> (Prims.op_Equality i.FStar_Ident.idText l.FStar_Ident.ident.FStar_Ident.idText))


let is_val : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, uu____18) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____19 -> begin
false
end))


let is_type : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____28, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun uu____63 -> (match (uu____63) with
| (t, uu____71) -> begin
(Prims.op_Equality (FStar_Parser_AST.id_of_tycon t) x.FStar_Ident.idText)
end))))
end
| uu____76 -> begin
false
end))


let definition_lids : FStar_Parser_AST.decl  ->  FStar_Ident.lid Prims.list = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____85, defs) -> begin
(FStar_Parser_AST.lids_of_let defs)
end
| FStar_Parser_AST.Tycon (uu____99, tys) -> begin
(FStar_All.pipe_right tys (FStar_List.collect (fun uu___206_140 -> (match (uu___206_140) with
| (FStar_Parser_AST.TyconAbbrev (id, uu____150, uu____151, uu____152), uu____153) -> begin
(

let uu____166 = (FStar_Ident.lid_of_ids ((id)::[]))
in (uu____166)::[])
end
| uu____167 -> begin
[]
end))))
end
| uu____174 -> begin
[]
end))


let is_definition_of : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (

let uu____183 = (definition_lids d)
in (FStar_Util.for_some (id_eq_lid x) uu____183)))


let rec prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (iface1) with
| [] -> begin
(([]), ((impl)::[]))
end
| (iface_hd)::iface_tl -> begin
(match (iface_hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____230, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___207_265 -> (match (uu___207_265) with
| (FStar_Parser_AST.TyconAbstract (uu____272), uu____273) -> begin
true
end
| uu____288 -> begin
false
end)))) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (impl.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let def_ids = (definition_lids impl)
in (

let defines_x = (FStar_Util.for_some (id_eq_lid x) def_ids)
in (match ((not (defines_x))) with
| true -> begin
(

let uu____317 = (FStar_All.pipe_right def_ids (FStar_Util.for_some (fun y -> (FStar_All.pipe_right iface_tl (FStar_Util.for_some (is_val y.FStar_Ident.ident))))))
in (match (uu____317) with
| true -> begin
(

let uu____332 = (

let uu____333 = (

let uu____338 = (

let uu____339 = (

let uu____340 = (FStar_All.pipe_right def_ids (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____340 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Expected the definition of %s to precede %s" x.FStar_Ident.idText uu____339))
in ((uu____338), (impl.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____333))
in (FStar_Exn.raise uu____332))
end
| uu____357 -> begin
((iface1), ((impl)::[]))
end))
end
| uu____362 -> begin
(

let mutually_defined_with_x = (FStar_All.pipe_right def_ids (FStar_List.filter (fun y -> (not ((id_eq_lid x y))))))
in (

let rec aux = (fun mutuals iface2 -> (match (((mutuals), (iface2))) with
| ([], uu____407) -> begin
(([]), (iface2))
end
| ((uu____418)::uu____419, []) -> begin
(([]), ([]))
end
| ((y)::ys, (iface_hd1)::iface_tl1) -> begin
(match ((is_val y.FStar_Ident.ident iface_hd1)) with
| true -> begin
(

let uu____450 = (aux ys iface_tl1)
in (match (uu____450) with
| (val_ys, iface3) -> begin
(((iface_hd1)::val_ys), (iface3))
end))
end
| uu____481 -> begin
(

let uu____482 = (

let uu____483 = (FStar_List.tryFind (is_val y.FStar_Ident.ident) iface_tl1)
in (FStar_All.pipe_left FStar_Option.isSome uu____483))
in (match (uu____482) with
| true -> begin
(

let uu____496 = (

let uu____497 = (

let uu____502 = (

let uu____503 = (FStar_Parser_AST.decl_to_string iface_hd1)
in (

let uu____504 = (FStar_Ident.string_of_lid y)
in (FStar_Util.format2 "%s is out of order with the definition of %s" uu____503 uu____504)))
in ((uu____502), (iface_hd1.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____497))
in (FStar_Exn.raise uu____496))
end
| uu____513 -> begin
(aux ys iface2)
end))
end)
end))
in (

let uu____514 = (aux mutually_defined_with_x iface_tl)
in (match (uu____514) with
| (take_iface, rest_iface) -> begin
((rest_iface), ((FStar_List.append ((iface_hd)::take_iface) ((impl)::[]))))
end))))
end)))
end
| uu____545 -> begin
(

let uu____546 = (prefix_with_iface_decls iface_tl impl)
in (match (uu____546) with
| (iface2, ds) -> begin
((iface2), ((iface_hd)::ds))
end))
end)
end))


let check_initial_interface : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface1 -> (

let rec aux = (fun iface2 -> (match (iface2) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(match (hd1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____599, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___208_634 -> (match (uu___208_634) with
| (FStar_Parser_AST.TyconAbstract (uu____641), uu____642) -> begin
true
end
| uu____657 -> begin
false
end)))) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (hd1.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let uu____666 = (FStar_Util.for_some (is_definition_of x) tl1)
in (match (uu____666) with
| true -> begin
(

let uu____667 = (

let uu____668 = (

let uu____673 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((uu____673), (hd1.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____668))
in (FStar_Exn.raise uu____667))
end
| uu____674 -> begin
(

let uu____675 = (FStar_All.pipe_right hd1.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____675) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Interfaces cannot use `assume val x : t`; just write `val x : t` instead"), (hd1.FStar_Parser_AST.drange)))))
end
| uu____676 -> begin
()
end))
end))
end
| uu____677 -> begin
()
end)
end))
in ((aux iface1);
(FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____686) -> begin
false
end
| uu____687 -> begin
true
end))));
)))


let rec ml_mode_prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____716, defs) -> begin
(

let xs = (FStar_Parser_AST.lids_of_let defs)
in (

let uu____733 = (FStar_List.partition (fun d -> (FStar_All.pipe_right xs (FStar_Util.for_some (fun x -> (is_val x.FStar_Ident.ident d))))) iface1)
in (match (uu____733) with
| (val_xs, rest_iface) -> begin
((rest_iface), ((FStar_List.append val_xs ((impl)::[]))))
end)))
end
| uu____770 -> begin
((iface1), ((impl)::[]))
end))


let ml_mode_check_initial_interface : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface1 -> (FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (uu____792) -> begin
true
end
| uu____797 -> begin
false
end)))))


let prefix_one_decl : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____826) -> begin
((iface1), ((impl)::[]))
end
| uu____831 -> begin
(

let uu____832 = (FStar_Options.ml_ish ())
in (match (uu____832) with
| true -> begin
(ml_mode_prefix_with_iface_decls iface1 impl)
end
| uu____841 -> begin
(prefix_with_iface_decls iface1 impl)
end))
end))


let initialize_interface : FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.unit FStar_ToSyntax_Env.withenv = (fun mname l env -> (

let decls = (

let uu____866 = (FStar_Options.ml_ish ())
in (match (uu____866) with
| true -> begin
(ml_mode_check_initial_interface l)
end
| uu____869 -> begin
(check_initial_interface l)
end))
in (

let uu____870 = (FStar_ToSyntax_Env.iface_decls env mname)
in (match (uu____870) with
| FStar_Pervasives_Native.Some (uu____879) -> begin
(

let uu____884 = (

let uu____885 = (

let uu____890 = (

let uu____891 = (FStar_Ident.string_of_lid mname)
in (FStar_Util.format1 "Interface %s has already been processed" uu____891))
in ((uu____890), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____885))
in (FStar_Exn.raise uu____884))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____898 = (FStar_ToSyntax_Env.set_iface_decls env mname decls)
in ((()), (uu____898)))
end))))


let prefix_with_interface_decls : FStar_Parser_AST.decl  ->  FStar_Parser_AST.decl Prims.list FStar_ToSyntax_Env.withenv = (fun impl env -> (

let uu____916 = (

let uu____921 = (FStar_ToSyntax_Env.current_module env)
in (FStar_ToSyntax_Env.iface_decls env uu____921))
in (match (uu____916) with
| FStar_Pervasives_Native.None -> begin
(((impl)::[]), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____937 = (prefix_one_decl iface1 impl)
in (match (uu____937) with
| (iface2, impl1) -> begin
(

let env1 = (

let uu____963 = (FStar_ToSyntax_Env.current_module env)
in (FStar_ToSyntax_Env.set_iface_decls env uu____963 iface2))
in ((impl1), (env1)))
end))
end)))


let interleave_module : FStar_Parser_AST.modul  ->  Prims.bool  ->  FStar_Parser_AST.modul FStar_ToSyntax_Env.withenv = (fun a expect_complete_modul env -> (match (a) with
| FStar_Parser_AST.Interface (uu____987) -> begin
((a), (env))
end
| FStar_Parser_AST.Module (l, impls) -> begin
(

let uu____1002 = (FStar_ToSyntax_Env.iface_decls env l)
in (match (uu____1002) with
| FStar_Pervasives_Native.None -> begin
((a), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1018 = (FStar_List.fold_left (fun uu____1042 impl -> (match (uu____1042) with
| (iface2, impls1) -> begin
(

let uu____1070 = (prefix_one_decl iface2 impl)
in (match (uu____1070) with
| (iface3, impls') -> begin
((iface3), ((FStar_List.append impls1 impls')))
end))
end)) ((iface1), ([])) impls)
in (match (uu____1018) with
| (iface2, impls1) -> begin
(

let env1 = (FStar_ToSyntax_Env.set_iface_decls env l iface2)
in (

let a1 = FStar_Parser_AST.Module (((l), (impls1)))
in (match (iface2) with
| (uu____1127)::uu____1128 when expect_complete_modul -> begin
(

let err1 = (

let uu____1132 = (FStar_List.map FStar_Parser_AST.decl_to_string iface2)
in (FStar_All.pipe_right uu____1132 (FStar_String.concat "\n\t")))
in (

let uu____1137 = (

let uu____1138 = (

let uu____1143 = (

let uu____1144 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format2 "Some interface elements were not implemented by module %s:\n\t%s" uu____1144 err1))
in ((uu____1143), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____1138))
in (FStar_Exn.raise uu____1137)))
end
| uu____1149 -> begin
((a1), (env1))
end)))
end))
end))
end))




