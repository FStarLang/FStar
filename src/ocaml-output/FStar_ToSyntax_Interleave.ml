
open Prims
open FStar_Pervasives

let id_eq_lid : FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.bool = (fun i l -> (i.FStar_Ident.idText = l.FStar_Ident.ident.FStar_Ident.idText))


let is_val : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, uu____18) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____19 -> begin
false
end))


let is_type : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____28, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun uu____48 -> (match (uu____48) with
| (t, uu____53) -> begin
((FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText)
end))))
end
| uu____56 -> begin
false
end))


let definition_lids : FStar_Parser_AST.decl  ->  FStar_Ident.lid Prims.list = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____63, defs) -> begin
(FStar_Parser_AST.lids_of_let defs)
end
| FStar_Parser_AST.Tycon (uu____71, tys) -> begin
(FStar_All.pipe_right tys (FStar_List.collect (fun uu___197_96 -> (match (uu___197_96) with
| (FStar_Parser_AST.TyconAbbrev (id, uu____102, uu____103, uu____104), uu____105) -> begin
(

let uu____112 = (FStar_Ident.lid_of_ids ((id)::[]))
in (uu____112)::[])
end
| uu____113 -> begin
[]
end))))
end
| uu____117 -> begin
[]
end))


let is_definition_of : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (

let uu____126 = (definition_lids d)
in (FStar_Util.for_some (id_eq_lid x) uu____126)))


let rec prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (iface1) with
| [] -> begin
(([]), ((impl)::[]))
end
| (iface_hd)::iface_tl -> begin
(match (iface_hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____155, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___198_175 -> (match (uu___198_175) with
| (FStar_Parser_AST.TyconAbstract (uu____179), uu____180) -> begin
true
end
| uu____188 -> begin
false
end)))) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (impl.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let def_ids = (definition_lids impl)
in (

let defines_x = (FStar_Util.for_some (id_eq_lid x) def_ids)
in (match ((not (defines_x))) with
| true -> begin
(

let uu____205 = (FStar_All.pipe_right def_ids (FStar_Util.for_some (fun y -> (FStar_All.pipe_right iface_tl (FStar_Util.for_some (is_val y.FStar_Ident.ident))))))
in (match (uu____205) with
| true -> begin
(

let uu____214 = (

let uu____215 = (

let uu____218 = (

let uu____219 = (

let uu____220 = (FStar_All.pipe_right def_ids (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____220 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Expected the definition of %s to precede %s" x.FStar_Ident.idText uu____219))
in ((uu____218), (impl.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____215))
in (FStar_Pervasives.raise uu____214))
end
| uu____229 -> begin
((iface1), ((impl)::[]))
end))
end
| uu____232 -> begin
(

let mutually_defined_with_x = (FStar_All.pipe_right def_ids (FStar_List.filter (fun y -> (not ((id_eq_lid x y))))))
in (

let rec aux = (fun mutuals iface2 -> (match (((mutuals), (iface2))) with
| ([], uu____260) -> begin
(([]), (iface2))
end
| ((uu____266)::uu____267, []) -> begin
(([]), ([]))
end
| ((y)::ys, (iface_hd1)::iface_tl1) -> begin
(match ((is_val y.FStar_Ident.ident iface_hd1)) with
| true -> begin
(

let uu____285 = (aux ys iface_tl1)
in (match (uu____285) with
| (val_ys, iface3) -> begin
(((iface_hd1)::val_ys), (iface3))
end))
end
| uu____302 -> begin
(

let uu____303 = (

let uu____304 = (FStar_List.tryFind (is_val y.FStar_Ident.ident) iface_tl1)
in (FStar_All.pipe_left FStar_Option.isSome uu____304))
in (match (uu____303) with
| true -> begin
(

let uu____311 = (

let uu____312 = (

let uu____315 = (

let uu____316 = (FStar_Parser_AST.decl_to_string iface_hd1)
in (

let uu____317 = (FStar_Ident.string_of_lid y)
in (FStar_Util.format2 "%s is out of order with the definition of %s" uu____316 uu____317)))
in ((uu____315), (iface_hd1.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____312))
in (FStar_Pervasives.raise uu____311))
end
| uu____322 -> begin
(aux ys iface2)
end))
end)
end))
in (

let uu____323 = (aux mutually_defined_with_x iface_tl)
in (match (uu____323) with
| (take_iface, rest_iface) -> begin
((rest_iface), ((FStar_List.append ((iface_hd)::take_iface) ((impl)::[]))))
end))))
end)))
end
| uu____340 -> begin
(

let uu____341 = (prefix_with_iface_decls iface_tl impl)
in (match (uu____341) with
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
| FStar_Parser_AST.Tycon (uu____374, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___199_394 -> (match (uu___199_394) with
| (FStar_Parser_AST.TyconAbstract (uu____398), uu____399) -> begin
true
end
| uu____407 -> begin
false
end)))) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Interface contains an abstract \'type\' declaration; use \'val\' instead"), (hd1.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let uu____413 = (FStar_Util.for_some (is_definition_of x) tl1)
in (match (uu____413) with
| true -> begin
(

let uu____414 = (

let uu____415 = (

let uu____418 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((uu____418), (hd1.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____415))
in (FStar_Pervasives.raise uu____414))
end
| uu____419 -> begin
(

let uu____420 = (FStar_All.pipe_right hd1.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____420) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Interfaces cannot use `assume val x : t`; just write `val x : t` instead"), (hd1.FStar_Parser_AST.drange)))))
end
| uu____421 -> begin
()
end))
end))
end
| uu____422 -> begin
()
end)
end))
in ((aux iface1);
(FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____429) -> begin
false
end
| uu____430 -> begin
true
end))));
)))


let rec ml_mode_prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____449, defs) -> begin
(

let xs = (FStar_Parser_AST.lids_of_let defs)
in (

let uu____459 = (FStar_List.partition (fun d -> (FStar_All.pipe_right xs (FStar_Util.for_some (fun x -> (is_val x.FStar_Ident.ident d))))) iface1)
in (match (uu____459) with
| (val_xs, rest_iface) -> begin
((rest_iface), ((FStar_List.append val_xs ((impl)::[]))))
end)))
end
| uu____481 -> begin
((iface1), ((impl)::[]))
end))


let ml_mode_check_initial_interface : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface1 -> (FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (uu____496) -> begin
true
end
| uu____499 -> begin
false
end)))))


let prefix_one_decl : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____518) -> begin
((iface1), ((impl)::[]))
end
| uu____521 -> begin
(

let uu____522 = (FStar_Options.ml_ish ())
in (match (uu____522) with
| true -> begin
(ml_mode_prefix_with_iface_decls iface1 impl)
end
| uu____527 -> begin
(prefix_with_iface_decls iface1 impl)
end))
end))


let initialize_interface : FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun mname l env -> (

let decls = (

let uu____544 = (FStar_Options.ml_ish ())
in (match (uu____544) with
| true -> begin
(ml_mode_check_initial_interface l)
end
| uu____546 -> begin
(check_initial_interface l)
end))
in (

let uu____547 = (FStar_ToSyntax_Env.iface_decls env mname)
in (match (uu____547) with
| FStar_Pervasives_Native.Some (uu____550) -> begin
(

let uu____553 = (

let uu____554 = (

let uu____557 = (

let uu____558 = (FStar_Ident.string_of_lid mname)
in (FStar_Util.format1 "Interface %s has already been processed" uu____558))
in ((uu____557), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____554))
in (FStar_Pervasives.raise uu____553))
end
| FStar_Pervasives_Native.None -> begin
(FStar_ToSyntax_Env.set_iface_decls env mname decls)
end))))


let prefix_with_interface_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  (FStar_ToSyntax_Env.env * FStar_Parser_AST.decl Prims.list) = (fun env impl -> (

let uu____574 = (

let uu____577 = (FStar_ToSyntax_Env.current_module env)
in (FStar_ToSyntax_Env.iface_decls env uu____577))
in (match (uu____574) with
| FStar_Pervasives_Native.None -> begin
((env), ((impl)::[]))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____586 = (prefix_one_decl iface1 impl)
in (match (uu____586) with
| (iface2, impl1) -> begin
(

let env1 = (

let uu____601 = (FStar_ToSyntax_Env.current_module env)
in (FStar_ToSyntax_Env.set_iface_decls env uu____601 iface2))
in ((env1), (impl1)))
end))
end)))


let interleave_module : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  Prims.bool  ->  (FStar_ToSyntax_Env.env * FStar_Parser_AST.modul) = (fun env a expect_complete_modul -> (match (a) with
| FStar_Parser_AST.Interface (uu____619) -> begin
((env), (a))
end
| FStar_Parser_AST.Module (l, impls) -> begin
(

let uu____628 = (FStar_ToSyntax_Env.iface_decls env l)
in (match (uu____628) with
| FStar_Pervasives_Native.None -> begin
((env), (a))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____637 = (FStar_List.fold_left (fun uu____653 impl -> (match (uu____653) with
| (iface2, impls1) -> begin
(

let uu____669 = (prefix_one_decl iface2 impl)
in (match (uu____669) with
| (iface3, impls') -> begin
((iface3), ((FStar_List.append impls1 impls')))
end))
end)) ((iface1), ([])) impls)
in (match (uu____637) with
| (iface2, impls1) -> begin
(

let env1 = (FStar_ToSyntax_Env.set_iface_decls env l iface2)
in (

let a1 = FStar_Parser_AST.Module (((l), (impls1)))
in (match (iface2) with
| (uu____701)::uu____702 when expect_complete_modul -> begin
(

let err1 = (

let uu____705 = (FStar_List.map FStar_Parser_AST.decl_to_string iface2)
in (FStar_All.pipe_right uu____705 (FStar_String.concat "\n\t")))
in (

let uu____708 = (

let uu____709 = (

let uu____712 = (

let uu____713 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format2 "Some interface elements were not implemented by module %s:\n\t%s" uu____713 err1))
in ((uu____712), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____709))
in (FStar_Pervasives.raise uu____708)))
end
| uu____716 -> begin
((env1), (a1))
end)))
end))
end))
end))




