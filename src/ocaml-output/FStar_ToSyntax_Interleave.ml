
open Prims
open FStar_Pervasives

let id_eq_lid : FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.bool = (fun i l -> (Prims.op_Equality i.FStar_Ident.idText l.FStar_Ident.ident.FStar_Ident.idText))


let is_val : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, uu____27) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____29 -> begin
false
end))


let is_type : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____44, uu____45, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun uu____85 -> (match (uu____85) with
| (t, uu____94) -> begin
(Prims.op_Equality (FStar_Parser_AST.id_of_tycon t) x.FStar_Ident.idText)
end))))
end
| uu____100 -> begin
false
end))


let definition_lids : FStar_Parser_AST.decl  ->  FStar_Ident.lident Prims.list = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____112, defs) -> begin
(FStar_Parser_AST.lids_of_let defs)
end
| FStar_Parser_AST.Tycon (uu____126, uu____127, tys) -> begin
(FStar_All.pipe_right tys (FStar_List.collect (fun uu___177_172 -> (match (uu___177_172) with
| (FStar_Parser_AST.TyconAbbrev (id1, uu____182, uu____183, uu____184), uu____185) -> begin
(

let uu____198 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____198)::[])
end
| (FStar_Parser_AST.TyconRecord (id1, uu____200, uu____201, uu____202), uu____203) -> begin
(

let uu____236 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____236)::[])
end
| (FStar_Parser_AST.TyconVariant (id1, uu____238, uu____239, uu____240), uu____241) -> begin
(

let uu____284 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____284)::[])
end
| uu____285 -> begin
[]
end))))
end
| uu____292 -> begin
[]
end))


let is_definition_of : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (

let uu____305 = (definition_lids d)
in (FStar_Util.for_some (id_eq_lid x) uu____305)))


let rec prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (

let qualify_kremlin_private = (fun impl1 -> (

let krem_private = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_string ((("KremlinPrivate"), (impl1.FStar_Parser_AST.drange))))) impl1.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu___181_348 = impl1
in {FStar_Parser_AST.d = uu___181_348.FStar_Parser_AST.d; FStar_Parser_AST.drange = uu___181_348.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___181_348.FStar_Parser_AST.doc; FStar_Parser_AST.quals = uu___181_348.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = (krem_private)::impl1.FStar_Parser_AST.attrs})))
in (match (iface1) with
| [] -> begin
(([]), (((qualify_kremlin_private impl))::[]))
end
| (iface_hd)::iface_tl -> begin
(match (iface_hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____373, uu____374, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___178_414 -> (match (uu___178_414) with
| (FStar_Parser_AST.TyconAbstract (uu____422), uu____423) -> begin
true
end
| uu____439 -> begin
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

let uu____473 = (FStar_All.pipe_right def_ids (FStar_Util.for_some (fun y -> (FStar_All.pipe_right iface_tl (FStar_Util.for_some (is_val y.FStar_Ident.ident))))))
in (match (uu____473) with
| true -> begin
(

let uu____492 = (

let uu____498 = (

let uu____500 = (

let uu____502 = (FStar_All.pipe_right def_ids (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____502 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Expected the definition of %s to precede %s" x.FStar_Ident.idText uu____500))
in ((FStar_Errors.Fatal_WrongDefinitionOrder), (uu____498)))
in (FStar_Errors.raise_error uu____492 impl.FStar_Parser_AST.drange))
end
| uu____527 -> begin
((iface1), (((qualify_kremlin_private impl))::[]))
end))
end
| uu____533 -> begin
(

let mutually_defined_with_x = (FStar_All.pipe_right def_ids (FStar_List.filter (fun y -> (not ((id_eq_lid x y))))))
in (

let rec aux = (fun mutuals iface2 -> (match (((mutuals), (iface2))) with
| ([], uu____583) -> begin
(([]), (iface2))
end
| ((uu____594)::uu____595, []) -> begin
(([]), ([]))
end
| ((y)::ys, (iface_hd1)::iface_tl1) -> begin
(match ((is_val y.FStar_Ident.ident iface_hd1)) with
| true -> begin
(

let uu____627 = (aux ys iface_tl1)
in (match (uu____627) with
| (val_ys, iface3) -> begin
(((iface_hd1)::val_ys), (iface3))
end))
end
| uu____658 -> begin
(

let uu____660 = (

let uu____662 = (FStar_List.tryFind (is_val y.FStar_Ident.ident) iface_tl1)
in (FStar_All.pipe_left FStar_Option.isSome uu____662))
in (match (uu____660) with
| true -> begin
(

let uu____677 = (

let uu____683 = (

let uu____685 = (FStar_Parser_AST.decl_to_string iface_hd1)
in (

let uu____687 = (FStar_Ident.string_of_lid y)
in (FStar_Util.format2 "%s is out of order with the definition of %s" uu____685 uu____687)))
in ((FStar_Errors.Fatal_WrongDefinitionOrder), (uu____683)))
in (FStar_Errors.raise_error uu____677 iface_hd1.FStar_Parser_AST.drange))
end
| uu____699 -> begin
(aux ys iface2)
end))
end)
end))
in (

let uu____701 = (aux mutually_defined_with_x iface_tl)
in (match (uu____701) with
| (take_iface, rest_iface) -> begin
((rest_iface), ((FStar_List.append ((iface_hd)::take_iface) ((impl)::[]))))
end))))
end)))
end
| uu____732 -> begin
(

let uu____733 = (prefix_with_iface_decls iface_tl impl)
in (match (uu____733) with
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
| FStar_Parser_AST.Tycon (uu____790, uu____791, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___179_831 -> (match (uu___179_831) with
| (FStar_Parser_AST.TyconAbstract (uu____839), uu____840) -> begin
true
end
| uu____856 -> begin
false
end)))) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AbstractTypeDeclarationInInterface), ("Interface contains an abstract \'type\' declaration; use \'val\' instead")) hd1.FStar_Parser_AST.drange)
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let uu____868 = (FStar_Util.for_some (is_definition_of x) tl1)
in (match (uu____868) with
| true -> begin
(

let uu____871 = (

let uu____877 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((FStar_Errors.Fatal_BothValAndLetInInterface), (uu____877)))
in (FStar_Errors.raise_error uu____871 hd1.FStar_Parser_AST.drange))
end
| uu____881 -> begin
(

let uu____883 = (FStar_All.pipe_right hd1.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____883) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AssumeValInInterface), ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead")) hd1.FStar_Parser_AST.drange)
end
| uu____891 -> begin
()
end))
end))
end
| uu____893 -> begin
()
end)
end))
in ((aux iface1);
(FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____903) -> begin
false
end
| uu____905 -> begin
true
end))));
)))


let rec ml_mode_prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____938, defs) -> begin
(

let xs = (FStar_Parser_AST.lids_of_let defs)
in (

let uu____955 = (FStar_List.partition (fun d -> (FStar_All.pipe_right xs (FStar_Util.for_some (fun x -> (is_val x.FStar_Ident.ident d))))) iface1)
in (match (uu____955) with
| (val_xs, rest_iface) -> begin
((rest_iface), ((FStar_List.append val_xs ((impl)::[]))))
end)))
end
| uu____993 -> begin
((iface1), ((impl)::[]))
end))


let ml_mode_check_initial_interface : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface1 -> (FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (uu____1018) -> begin
true
end
| uu____1024 -> begin
false
end)))))


let prefix_one_decl : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____1057) -> begin
((iface1), ((impl)::[]))
end
| uu____1062 -> begin
(

let uu____1063 = (FStar_Options.ml_ish ())
in (match (uu____1063) with
| true -> begin
(ml_mode_prefix_with_iface_decls iface1 impl)
end
| uu____1074 -> begin
(prefix_with_iface_decls iface1 impl)
end))
end))


let initialize_interface : FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  unit FStar_Syntax_DsEnv.withenv = (fun mname l env -> (

let decls = (

let uu____1105 = (FStar_Options.ml_ish ())
in (match (uu____1105) with
| true -> begin
(ml_mode_check_initial_interface l)
end
| uu____1110 -> begin
(check_initial_interface l)
end))
in (

let uu____1112 = (FStar_Syntax_DsEnv.iface_decls env mname)
in (match (uu____1112) with
| FStar_Pervasives_Native.Some (uu____1121) -> begin
(

let uu____1126 = (

let uu____1132 = (

let uu____1134 = (FStar_Ident.string_of_lid mname)
in (FStar_Util.format1 "Interface %s has already been processed" uu____1134))
in ((FStar_Errors.Fatal_InterfaceAlreadyProcessed), (uu____1132)))
in (

let uu____1138 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____1126 uu____1138)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1145 = (FStar_Syntax_DsEnv.set_iface_decls env mname decls)
in ((()), (uu____1145)))
end))))


let prefix_with_interface_decls : FStar_Parser_AST.decl  ->  FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv = (fun impl env -> (

let uu____1167 = (

let uu____1172 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Syntax_DsEnv.iface_decls env uu____1172))
in (match (uu____1167) with
| FStar_Pervasives_Native.None -> begin
(((impl)::[]), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1188 = (prefix_one_decl iface1 impl)
in (match (uu____1188) with
| (iface2, impl1) -> begin
(

let env1 = (

let uu____1214 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Syntax_DsEnv.set_iface_decls env uu____1214 iface2))
in ((impl1), (env1)))
end))
end)))


let interleave_module : FStar_Parser_AST.modul  ->  Prims.bool  ->  FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv = (fun a expect_complete_modul env -> (match (a) with
| FStar_Parser_AST.Interface (uu____1245) -> begin
((a), (env))
end
| FStar_Parser_AST.Module (l, impls) -> begin
(

let uu____1261 = (FStar_Syntax_DsEnv.iface_decls env l)
in (match (uu____1261) with
| FStar_Pervasives_Native.None -> begin
((a), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1277 = (FStar_List.fold_left (fun uu____1301 impl -> (match (uu____1301) with
| (iface2, impls1) -> begin
(

let uu____1329 = (prefix_one_decl iface2 impl)
in (match (uu____1329) with
| (iface3, impls') -> begin
((iface3), ((FStar_List.append impls1 impls')))
end))
end)) ((iface1), ([])) impls)
in (match (uu____1277) with
| (iface2, impls1) -> begin
(

let uu____1378 = (

let uu____1387 = (FStar_Util.prefix_until (fun uu___180_1406 -> (match (uu___180_1406) with
| {FStar_Parser_AST.d = FStar_Parser_AST.Val (uu____1408); FStar_Parser_AST.drange = uu____1409; FStar_Parser_AST.doc = uu____1410; FStar_Parser_AST.quals = uu____1411; FStar_Parser_AST.attrs = uu____1412} -> begin
true
end
| uu____1420 -> begin
false
end)) iface2)
in (match (uu____1387) with
| FStar_Pervasives_Native.None -> begin
((iface2), ([]))
end
| FStar_Pervasives_Native.Some (lets, one_val, rest) -> begin
((lets), ((one_val)::rest))
end))
in (match (uu____1378) with
| (iface_lets, remaining_iface_vals) -> begin
(

let impls2 = (FStar_List.append impls1 iface_lets)
in (

let env1 = (

let uu____1487 = (FStar_Options.interactive ())
in (match (uu____1487) with
| true -> begin
(FStar_Syntax_DsEnv.set_iface_decls env l remaining_iface_vals)
end
| uu____1490 -> begin
env
end))
in (

let a1 = FStar_Parser_AST.Module (((l), (impls2)))
in (match (remaining_iface_vals) with
| (uu____1499)::uu____1500 when expect_complete_modul -> begin
(

let err = (

let uu____1505 = (FStar_List.map FStar_Parser_AST.decl_to_string remaining_iface_vals)
in (FStar_All.pipe_right uu____1505 (FStar_String.concat "\n\t")))
in (

let uu____1515 = (

let uu____1521 = (

let uu____1523 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format2 "Some interface elements were not implemented by module %s:\n\t%s" uu____1523 err))
in ((FStar_Errors.Fatal_InterfaceNotImplementedByModule), (uu____1521)))
in (

let uu____1527 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____1515 uu____1527))))
end
| uu____1532 -> begin
((a1), (env1))
end))))
end))
end))
end))
end))




