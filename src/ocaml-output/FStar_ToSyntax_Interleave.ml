
open Prims
open FStar_Pervasives

let id_eq_lid : FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.bool = (fun i l -> (Prims.op_Equality i.FStar_Ident.idText l.FStar_Ident.ident.FStar_Ident.idText))


let is_val : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (y, uu____14) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____15 -> begin
false
end))


let is_type : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____22, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun uu____57 -> (match (uu____57) with
| (t, uu____65) -> begin
(Prims.op_Equality (FStar_Parser_AST.id_of_tycon t) x.FStar_Ident.idText)
end))))
end
| uu____70 -> begin
false
end))


let definition_lids : FStar_Parser_AST.decl  ->  FStar_Ident.lid Prims.list = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____78, defs) -> begin
(FStar_Parser_AST.lids_of_let defs)
end
| FStar_Parser_AST.Tycon (uu____92, tys) -> begin
(FStar_All.pipe_right tys (FStar_List.collect (fun uu___60_133 -> (match (uu___60_133) with
| (FStar_Parser_AST.TyconAbbrev (id1, uu____143, uu____144, uu____145), uu____146) -> begin
(

let uu____159 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____159)::[])
end
| (FStar_Parser_AST.TyconRecord (id1, uu____161, uu____162, uu____163), uu____164) -> begin
(

let uu____197 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____197)::[])
end
| (FStar_Parser_AST.TyconVariant (id1, uu____199, uu____200, uu____201), uu____202) -> begin
(

let uu____243 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____243)::[])
end
| uu____244 -> begin
[]
end))))
end
| uu____251 -> begin
[]
end))


let is_definition_of : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (

let uu____258 = (definition_lids d)
in (FStar_Util.for_some (id_eq_lid x) uu____258)))


let rec prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (

let qualify_kremlin_private = (fun impl1 -> (

let krem_private = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_string ((("KremlinPrivate"), (impl1.FStar_Parser_AST.drange))))) impl1.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu___64_292 = impl1
in {FStar_Parser_AST.d = uu___64_292.FStar_Parser_AST.d; FStar_Parser_AST.drange = uu___64_292.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___64_292.FStar_Parser_AST.doc; FStar_Parser_AST.quals = uu___64_292.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = (krem_private)::impl1.FStar_Parser_AST.attrs})))
in (match (iface1) with
| [] -> begin
(([]), (((qualify_kremlin_private impl))::[]))
end
| (iface_hd)::iface_tl -> begin
(match (iface_hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____317, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___61_352 -> (match (uu___61_352) with
| (FStar_Parser_AST.TyconAbstract (uu____359), uu____360) -> begin
true
end
| uu____375 -> begin
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

let uu____404 = (FStar_All.pipe_right def_ids (FStar_Util.for_some (fun y -> (FStar_All.pipe_right iface_tl (FStar_Util.for_some (is_val y.FStar_Ident.ident))))))
in (match (uu____404) with
| true -> begin
(

let uu____419 = (

let uu____424 = (

let uu____425 = (

let uu____426 = (FStar_All.pipe_right def_ids (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____426 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Expected the definition of %s to precede %s" x.FStar_Ident.idText uu____425))
in ((FStar_Errors.Fatal_WrongDefinitionOrder), (uu____424)))
in (FStar_Errors.raise_error uu____419 impl.FStar_Parser_AST.drange))
end
| uu____443 -> begin
((iface1), (((qualify_kremlin_private impl))::[]))
end))
end
| uu____448 -> begin
(

let mutually_defined_with_x = (FStar_All.pipe_right def_ids (FStar_List.filter (fun y -> (not ((id_eq_lid x y))))))
in (

let rec aux = (fun mutuals iface2 -> (match (((mutuals), (iface2))) with
| ([], uu____493) -> begin
(([]), (iface2))
end
| ((uu____504)::uu____505, []) -> begin
(([]), ([]))
end
| ((y)::ys, (iface_hd1)::iface_tl1) -> begin
(match ((is_val y.FStar_Ident.ident iface_hd1)) with
| true -> begin
(

let uu____536 = (aux ys iface_tl1)
in (match (uu____536) with
| (val_ys, iface3) -> begin
(((iface_hd1)::val_ys), (iface3))
end))
end
| uu____567 -> begin
(

let uu____568 = (

let uu____569 = (FStar_List.tryFind (is_val y.FStar_Ident.ident) iface_tl1)
in (FStar_All.pipe_left FStar_Option.isSome uu____569))
in (match (uu____568) with
| true -> begin
(

let uu____582 = (

let uu____587 = (

let uu____588 = (FStar_Parser_AST.decl_to_string iface_hd1)
in (

let uu____589 = (FStar_Ident.string_of_lid y)
in (FStar_Util.format2 "%s is out of order with the definition of %s" uu____588 uu____589)))
in ((FStar_Errors.Fatal_WrongDefinitionOrder), (uu____587)))
in (FStar_Errors.raise_error uu____582 iface_hd1.FStar_Parser_AST.drange))
end
| uu____598 -> begin
(aux ys iface2)
end))
end)
end))
in (

let uu____599 = (aux mutually_defined_with_x iface_tl)
in (match (uu____599) with
| (take_iface, rest_iface) -> begin
((rest_iface), ((FStar_List.append ((iface_hd)::take_iface) ((impl)::[]))))
end))))
end)))
end
| uu____630 -> begin
(

let uu____631 = (prefix_with_iface_decls iface_tl impl)
in (match (uu____631) with
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
| FStar_Parser_AST.Tycon (uu____683, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___62_718 -> (match (uu___62_718) with
| (FStar_Parser_AST.TyconAbstract (uu____725), uu____726) -> begin
true
end
| uu____741 -> begin
false
end)))) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AbstractTypeDeclarationInInterface), ("Interface contains an abstract \'type\' declaration; use \'val\' instead")) hd1.FStar_Parser_AST.drange)
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let uu____750 = (FStar_Util.for_some (is_definition_of x) tl1)
in (match (uu____750) with
| true -> begin
(

let uu____751 = (

let uu____756 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((FStar_Errors.Fatal_BothValAndLetInInterface), (uu____756)))
in (FStar_Errors.raise_error uu____751 hd1.FStar_Parser_AST.drange))
end
| uu____757 -> begin
(

let uu____758 = (FStar_All.pipe_right hd1.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____758) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AssumeValInInterface), ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead")) hd1.FStar_Parser_AST.drange)
end
| uu____759 -> begin
()
end))
end))
end
| uu____760 -> begin
()
end)
end))
in ((aux iface1);
(FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____769) -> begin
false
end
| uu____770 -> begin
true
end))));
)))


let rec ml_mode_prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____797, defs) -> begin
(

let xs = (FStar_Parser_AST.lids_of_let defs)
in (

let uu____814 = (FStar_List.partition (fun d -> (FStar_All.pipe_right xs (FStar_Util.for_some (fun x -> (is_val x.FStar_Ident.ident d))))) iface1)
in (match (uu____814) with
| (val_xs, rest_iface) -> begin
((rest_iface), ((FStar_List.append val_xs ((impl)::[]))))
end)))
end
| uu____851 -> begin
((iface1), ((impl)::[]))
end))


let ml_mode_check_initial_interface : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface1 -> (FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (uu____872) -> begin
true
end
| uu____877 -> begin
false
end)))))


let prefix_one_decl : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____904) -> begin
((iface1), ((impl)::[]))
end
| uu____909 -> begin
(

let uu____910 = (FStar_Options.ml_ish ())
in (match (uu____910) with
| true -> begin
(ml_mode_prefix_with_iface_decls iface1 impl)
end
| uu____919 -> begin
(prefix_with_iface_decls iface1 impl)
end))
end))


let initialize_interface : FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.unit FStar_Syntax_DsEnv.withenv = (fun mname l env -> (

let decls = (

let uu____942 = (FStar_Options.ml_ish ())
in (match (uu____942) with
| true -> begin
(ml_mode_check_initial_interface l)
end
| uu____945 -> begin
(check_initial_interface l)
end))
in (

let uu____946 = (FStar_Syntax_DsEnv.iface_decls env mname)
in (match (uu____946) with
| FStar_Pervasives_Native.Some (uu____955) -> begin
(

let uu____960 = (

let uu____965 = (

let uu____966 = (FStar_Ident.string_of_lid mname)
in (FStar_Util.format1 "Interface %s has already been processed" uu____966))
in ((FStar_Errors.Fatal_InterfaceAlreadyProcessed), (uu____965)))
in (FStar_Errors.raise_error uu____960 (FStar_Ident.range_of_lid mname)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____973 = (FStar_Syntax_DsEnv.set_iface_decls env mname decls)
in ((()), (uu____973)))
end))))


let prefix_with_interface_decls : FStar_Parser_AST.decl  ->  FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv = (fun impl env -> (

let uu____990 = (

let uu____995 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Syntax_DsEnv.iface_decls env uu____995))
in (match (uu____990) with
| FStar_Pervasives_Native.None -> begin
(((impl)::[]), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1011 = (prefix_one_decl iface1 impl)
in (match (uu____1011) with
| (iface2, impl1) -> begin
(

let env1 = (

let uu____1037 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Syntax_DsEnv.set_iface_decls env uu____1037 iface2))
in ((impl1), (env1)))
end))
end)))


let interleave_module : FStar_Parser_AST.modul  ->  Prims.bool  ->  FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv = (fun a expect_complete_modul env -> (match (a) with
| FStar_Parser_AST.Interface (uu____1059) -> begin
((a), (env))
end
| FStar_Parser_AST.Module (l, impls) -> begin
(

let uu____1074 = (FStar_Syntax_DsEnv.iface_decls env l)
in (match (uu____1074) with
| FStar_Pervasives_Native.None -> begin
((a), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1090 = (FStar_List.fold_left (fun uu____1114 impl -> (match (uu____1114) with
| (iface2, impls1) -> begin
(

let uu____1142 = (prefix_one_decl iface2 impl)
in (match (uu____1142) with
| (iface3, impls') -> begin
((iface3), ((FStar_List.append impls1 impls')))
end))
end)) ((iface1), ([])) impls)
in (match (uu____1090) with
| (iface2, impls1) -> begin
(

let uu____1191 = (

let uu____1200 = (FStar_Util.prefix_until (fun uu___63_1219 -> (match (uu___63_1219) with
| {FStar_Parser_AST.d = FStar_Parser_AST.Val (uu____1220); FStar_Parser_AST.drange = uu____1221; FStar_Parser_AST.doc = uu____1222; FStar_Parser_AST.quals = uu____1223; FStar_Parser_AST.attrs = uu____1224} -> begin
true
end
| uu____1231 -> begin
false
end)) iface2)
in (match (uu____1200) with
| FStar_Pervasives_Native.None -> begin
((iface2), ([]))
end
| FStar_Pervasives_Native.Some (lets, one_val, rest) -> begin
((lets), ((one_val)::rest))
end))
in (match (uu____1191) with
| (iface_lets, remaining_iface_vals) -> begin
(

let impls2 = (FStar_List.append impls1 iface_lets)
in (

let env1 = (FStar_Syntax_DsEnv.set_iface_decls env l remaining_iface_vals)
in (

let a1 = FStar_Parser_AST.Module (((l), (impls2)))
in (match (remaining_iface_vals) with
| (uu____1304)::uu____1305 when expect_complete_modul -> begin
(

let err = (

let uu____1309 = (FStar_List.map FStar_Parser_AST.decl_to_string remaining_iface_vals)
in (FStar_All.pipe_right uu____1309 (FStar_String.concat "\n\t")))
in (

let uu____1314 = (

let uu____1319 = (

let uu____1320 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format2 "Some interface elements were not implemented by module %s:\n\t%s" uu____1320 err))
in ((FStar_Errors.Fatal_InterfaceNotImplementedByModule), (uu____1319)))
in (FStar_Errors.raise_error uu____1314 (FStar_Ident.range_of_lid l))))
end
| uu____1325 -> begin
((a1), (env1))
end))))
end))
end))
end))
end))




