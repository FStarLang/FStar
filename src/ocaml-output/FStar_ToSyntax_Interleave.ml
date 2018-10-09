
open Prims
open FStar_Pervasives

let id_eq_lid : FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.bool = (fun i l -> (Prims.op_Equality i.FStar_Ident.idText l.FStar_Ident.ident.FStar_Ident.idText))


let is_val : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, uu____22) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____23 -> begin
false
end))


let is_type : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____34, uu____35, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun uu____70 -> (match (uu____70) with
| (t, uu____78) -> begin
(Prims.op_Equality (FStar_Parser_AST.id_of_tycon t) x.FStar_Ident.idText)
end))))
end
| uu____83 -> begin
false
end))


let definition_lids : FStar_Parser_AST.decl  ->  FStar_Ident.lident Prims.list = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____93, defs) -> begin
(FStar_Parser_AST.lids_of_let defs)
end
| FStar_Parser_AST.Tycon (uu____107, uu____108, tys) -> begin
(FStar_All.pipe_right tys (FStar_List.collect (fun uu___175_149 -> (match (uu___175_149) with
| (FStar_Parser_AST.TyconAbbrev (id1, uu____159, uu____160, uu____161), uu____162) -> begin
(

let uu____175 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____175)::[])
end
| (FStar_Parser_AST.TyconRecord (id1, uu____177, uu____178, uu____179), uu____180) -> begin
(

let uu____213 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____213)::[])
end
| (FStar_Parser_AST.TyconVariant (id1, uu____215, uu____216, uu____217), uu____218) -> begin
(

let uu____259 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____259)::[])
end
| uu____260 -> begin
[]
end))))
end
| uu____267 -> begin
[]
end))


let is_definition_of : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (

let uu____278 = (definition_lids d)
in (FStar_Util.for_some (id_eq_lid x) uu____278)))


let rec prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (

let qualify_kremlin_private = (fun impl1 -> (

let krem_private = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_string ((("KremlinPrivate"), (impl1.FStar_Parser_AST.drange))))) impl1.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu___179_318 = impl1
in {FStar_Parser_AST.d = uu___179_318.FStar_Parser_AST.d; FStar_Parser_AST.drange = uu___179_318.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___179_318.FStar_Parser_AST.doc; FStar_Parser_AST.quals = uu___179_318.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = (krem_private)::impl1.FStar_Parser_AST.attrs})))
in (match (iface1) with
| [] -> begin
(([]), (((qualify_kremlin_private impl))::[]))
end
| (iface_hd)::iface_tl -> begin
(match (iface_hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____343, uu____344, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___176_379 -> (match (uu___176_379) with
| (FStar_Parser_AST.TyconAbstract (uu____386), uu____387) -> begin
true
end
| uu____402 -> begin
false
end)))) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AbstractTypeDeclarationInInterface), ("Interface contains an abstract \'type\' declaration; use \'val\' instead")) impl.FStar_Parser_AST.drange)
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let def_ids = (definition_lids impl)
in (

let defines_x = (FStar_Util.for_some (id_eq_lid x) def_ids)
in (match ((not (defines_x))) with
| true -> begin
(

let uu____431 = (FStar_All.pipe_right def_ids (FStar_Util.for_some (fun y -> (FStar_All.pipe_right iface_tl (FStar_Util.for_some (is_val y.FStar_Ident.ident))))))
in (match (uu____431) with
| true -> begin
(

let uu____446 = (

let uu____451 = (

let uu____452 = (

let uu____453 = (FStar_All.pipe_right def_ids (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____453 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Expected the definition of %s to precede %s" x.FStar_Ident.idText uu____452))
in ((FStar_Errors.Fatal_WrongDefinitionOrder), (uu____451)))
in (FStar_Errors.raise_error uu____446 impl.FStar_Parser_AST.drange))
end
| uu____470 -> begin
((iface1), (((qualify_kremlin_private impl))::[]))
end))
end
| uu____475 -> begin
(

let mutually_defined_with_x = (FStar_All.pipe_right def_ids (FStar_List.filter (fun y -> (not ((id_eq_lid x y))))))
in (

let rec aux = (fun mutuals iface2 -> (match (((mutuals), (iface2))) with
| ([], uu____524) -> begin
(([]), (iface2))
end
| ((uu____535)::uu____536, []) -> begin
(([]), ([]))
end
| ((y)::ys, (iface_hd1)::iface_tl1) -> begin
(match ((is_val y.FStar_Ident.ident iface_hd1)) with
| true -> begin
(

let uu____567 = (aux ys iface_tl1)
in (match (uu____567) with
| (val_ys, iface3) -> begin
(((iface_hd1)::val_ys), (iface3))
end))
end
| uu____598 -> begin
(

let uu____599 = (

let uu____600 = (FStar_List.tryFind (is_val y.FStar_Ident.ident) iface_tl1)
in (FStar_All.pipe_left FStar_Option.isSome uu____600))
in (match (uu____599) with
| true -> begin
(

let uu____613 = (

let uu____618 = (

let uu____619 = (FStar_Parser_AST.decl_to_string iface_hd1)
in (

let uu____620 = (FStar_Ident.string_of_lid y)
in (FStar_Util.format2 "%s is out of order with the definition of %s" uu____619 uu____620)))
in ((FStar_Errors.Fatal_WrongDefinitionOrder), (uu____618)))
in (FStar_Errors.raise_error uu____613 iface_hd1.FStar_Parser_AST.drange))
end
| uu____629 -> begin
(aux ys iface2)
end))
end)
end))
in (

let uu____630 = (aux mutually_defined_with_x iface_tl)
in (match (uu____630) with
| (take_iface, rest_iface) -> begin
((rest_iface), ((FStar_List.append ((iface_hd)::take_iface) ((impl)::[]))))
end))))
end)))
end
| uu____661 -> begin
(

let uu____662 = (prefix_with_iface_decls iface_tl impl)
in (match (uu____662) with
| (iface2, ds) -> begin
((iface2), ((iface_hd)::ds))
end))
end)
end)))


let check_initial_interface : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface1 -> (

let rec aux = (fun iface2 -> (match (iface2) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(match (hd1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____718, uu____719, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___177_754 -> (match (uu___177_754) with
| (FStar_Parser_AST.TyconAbstract (uu____761), uu____762) -> begin
true
end
| uu____777 -> begin
false
end)))) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AbstractTypeDeclarationInInterface), ("Interface contains an abstract \'type\' declaration; use \'val\' instead")) hd1.FStar_Parser_AST.drange)
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let uu____786 = (FStar_Util.for_some (is_definition_of x) tl1)
in (match (uu____786) with
| true -> begin
(

let uu____787 = (

let uu____792 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((FStar_Errors.Fatal_BothValAndLetInInterface), (uu____792)))
in (FStar_Errors.raise_error uu____787 hd1.FStar_Parser_AST.drange))
end
| uu____793 -> begin
(

let uu____794 = (FStar_All.pipe_right hd1.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____794) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AssumeValInInterface), ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead")) hd1.FStar_Parser_AST.drange)
end
| uu____797 -> begin
()
end))
end))
end
| uu____798 -> begin
()
end)
end))
in ((aux iface1);
(FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____807) -> begin
false
end
| uu____808 -> begin
true
end))));
)))


let rec ml_mode_prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____839, defs) -> begin
(

let xs = (FStar_Parser_AST.lids_of_let defs)
in (

let uu____856 = (FStar_List.partition (fun d -> (FStar_All.pipe_right xs (FStar_Util.for_some (fun x -> (is_val x.FStar_Ident.ident d))))) iface1)
in (match (uu____856) with
| (val_xs, rest_iface) -> begin
((rest_iface), ((FStar_List.append val_xs ((impl)::[]))))
end)))
end
| uu____893 -> begin
((iface1), ((impl)::[]))
end))


let ml_mode_check_initial_interface : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface1 -> (FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (uu____916) -> begin
true
end
| uu____921 -> begin
false
end)))))


let prefix_one_decl : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____952) -> begin
((iface1), ((impl)::[]))
end
| uu____957 -> begin
(

let uu____958 = (FStar_Options.ml_ish ())
in (match (uu____958) with
| true -> begin
(ml_mode_prefix_with_iface_decls iface1 impl)
end
| uu____967 -> begin
(prefix_with_iface_decls iface1 impl)
end))
end))


let initialize_interface : FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  unit FStar_Syntax_DsEnv.withenv = (fun mname l env -> (

let decls = (

let uu____996 = (FStar_Options.ml_ish ())
in (match (uu____996) with
| true -> begin
(ml_mode_check_initial_interface l)
end
| uu____999 -> begin
(check_initial_interface l)
end))
in (

let uu____1000 = (FStar_Syntax_DsEnv.iface_decls env mname)
in (match (uu____1000) with
| FStar_Pervasives_Native.Some (uu____1009) -> begin
(

let uu____1014 = (

let uu____1019 = (

let uu____1020 = (FStar_Ident.string_of_lid mname)
in (FStar_Util.format1 "Interface %s has already been processed" uu____1020))
in ((FStar_Errors.Fatal_InterfaceAlreadyProcessed), (uu____1019)))
in (

let uu____1021 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____1014 uu____1021)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1028 = (FStar_Syntax_DsEnv.set_iface_decls env mname decls)
in ((()), (uu____1028)))
end))))


let prefix_with_interface_decls : FStar_Parser_AST.decl  ->  FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv = (fun impl env -> (

let uu____1049 = (

let uu____1054 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Syntax_DsEnv.iface_decls env uu____1054))
in (match (uu____1049) with
| FStar_Pervasives_Native.None -> begin
(((impl)::[]), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1070 = (prefix_one_decl iface1 impl)
in (match (uu____1070) with
| (iface2, impl1) -> begin
(

let env1 = (

let uu____1096 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Syntax_DsEnv.set_iface_decls env uu____1096 iface2))
in ((impl1), (env1)))
end))
end)))


let interleave_module : FStar_Parser_AST.modul  ->  Prims.bool  ->  FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv = (fun a expect_complete_modul env -> (match (a) with
| FStar_Parser_AST.Interface (uu____1124) -> begin
((a), (env))
end
| FStar_Parser_AST.Module (l, impls) -> begin
(

let uu____1139 = (FStar_Syntax_DsEnv.iface_decls env l)
in (match (uu____1139) with
| FStar_Pervasives_Native.None -> begin
((a), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1155 = (FStar_List.fold_left (fun uu____1179 impl -> (match (uu____1179) with
| (iface2, impls1) -> begin
(

let uu____1207 = (prefix_one_decl iface2 impl)
in (match (uu____1207) with
| (iface3, impls') -> begin
((iface3), ((FStar_List.append impls1 impls')))
end))
end)) ((iface1), ([])) impls)
in (match (uu____1155) with
| (iface2, impls1) -> begin
(

let uu____1256 = (

let uu____1265 = (FStar_Util.prefix_until (fun uu___178_1284 -> (match (uu___178_1284) with
| {FStar_Parser_AST.d = FStar_Parser_AST.Val (uu____1285); FStar_Parser_AST.drange = uu____1286; FStar_Parser_AST.doc = uu____1287; FStar_Parser_AST.quals = uu____1288; FStar_Parser_AST.attrs = uu____1289} -> begin
true
end
| uu____1296 -> begin
false
end)) iface2)
in (match (uu____1265) with
| FStar_Pervasives_Native.None -> begin
((iface2), ([]))
end
| FStar_Pervasives_Native.Some (lets, one_val, rest) -> begin
((lets), ((one_val)::rest))
end))
in (match (uu____1256) with
| (iface_lets, remaining_iface_vals) -> begin
(

let impls2 = (FStar_List.append impls1 iface_lets)
in (

let env1 = (FStar_Syntax_DsEnv.set_iface_decls env l remaining_iface_vals)
in (

let a1 = FStar_Parser_AST.Module (((l), (impls2)))
in (match (remaining_iface_vals) with
| (uu____1369)::uu____1370 when expect_complete_modul -> begin
(

let err = (

let uu____1374 = (FStar_List.map FStar_Parser_AST.decl_to_string remaining_iface_vals)
in (FStar_All.pipe_right uu____1374 (FStar_String.concat "\n\t")))
in (

let uu____1379 = (

let uu____1384 = (

let uu____1385 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format2 "Some interface elements were not implemented by module %s:\n\t%s" uu____1385 err))
in ((FStar_Errors.Fatal_InterfaceNotImplementedByModule), (uu____1384)))
in (

let uu____1386 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____1379 uu____1386))))
end
| uu____1391 -> begin
((a1), (env1))
end))))
end))
end))
end))
end))




