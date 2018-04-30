
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
| FStar_Parser_AST.Tycon (uu____34, tys) -> begin
(FStar_All.pipe_right tys (FStar_Util.for_some (fun uu____69 -> (match (uu____69) with
| (t, uu____77) -> begin
(Prims.op_Equality (FStar_Parser_AST.id_of_tycon t) x.FStar_Ident.idText)
end))))
end
| uu____82 -> begin
false
end))


let definition_lids : FStar_Parser_AST.decl  ->  FStar_Ident.lident Prims.list = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____92, defs) -> begin
(FStar_Parser_AST.lids_of_let defs)
end
| FStar_Parser_AST.Tycon (uu____106, tys) -> begin
(FStar_All.pipe_right tys (FStar_List.collect (fun uu___59_147 -> (match (uu___59_147) with
| (FStar_Parser_AST.TyconAbbrev (id1, uu____157, uu____158, uu____159), uu____160) -> begin
(

let uu____173 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____173)::[])
end
| (FStar_Parser_AST.TyconRecord (id1, uu____175, uu____176, uu____177), uu____178) -> begin
(

let uu____211 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____211)::[])
end
| (FStar_Parser_AST.TyconVariant (id1, uu____213, uu____214, uu____215), uu____216) -> begin
(

let uu____257 = (FStar_Ident.lid_of_ids ((id1)::[]))
in (uu____257)::[])
end
| uu____258 -> begin
[]
end))))
end
| uu____265 -> begin
[]
end))


let is_definition_of : FStar_Ident.ident  ->  FStar_Parser_AST.decl  ->  Prims.bool = (fun x d -> (

let uu____276 = (definition_lids d)
in (FStar_Util.for_some (id_eq_lid x) uu____276)))


let rec prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (

let qualify_kremlin_private = (fun impl1 -> (

let krem_private = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_string ((("KremlinPrivate"), (impl1.FStar_Parser_AST.drange))))) impl1.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu___63_316 = impl1
in {FStar_Parser_AST.d = uu___63_316.FStar_Parser_AST.d; FStar_Parser_AST.drange = uu___63_316.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___63_316.FStar_Parser_AST.doc; FStar_Parser_AST.quals = uu___63_316.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = (krem_private)::impl1.FStar_Parser_AST.attrs})))
in (match (iface1) with
| [] -> begin
(([]), (((qualify_kremlin_private impl))::[]))
end
| (iface_hd)::iface_tl -> begin
(match (iface_hd.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____341, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___60_376 -> (match (uu___60_376) with
| (FStar_Parser_AST.TyconAbstract (uu____383), uu____384) -> begin
true
end
| uu____399 -> begin
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

let uu____428 = (FStar_All.pipe_right def_ids (FStar_Util.for_some (fun y -> (FStar_All.pipe_right iface_tl (FStar_Util.for_some (is_val y.FStar_Ident.ident))))))
in (match (uu____428) with
| true -> begin
(

let uu____443 = (

let uu____448 = (

let uu____449 = (

let uu____450 = (FStar_All.pipe_right def_ids (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____450 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Expected the definition of %s to precede %s" x.FStar_Ident.idText uu____449))
in ((FStar_Errors.Fatal_WrongDefinitionOrder), (uu____448)))
in (FStar_Errors.raise_error uu____443 impl.FStar_Parser_AST.drange))
end
| uu____467 -> begin
((iface1), (((qualify_kremlin_private impl))::[]))
end))
end
| uu____472 -> begin
(

let mutually_defined_with_x = (FStar_All.pipe_right def_ids (FStar_List.filter (fun y -> (not ((id_eq_lid x y))))))
in (

let rec aux = (fun mutuals iface2 -> (match (((mutuals), (iface2))) with
| ([], uu____521) -> begin
(([]), (iface2))
end
| ((uu____532)::uu____533, []) -> begin
(([]), ([]))
end
| ((y)::ys, (iface_hd1)::iface_tl1) -> begin
(match ((is_val y.FStar_Ident.ident iface_hd1)) with
| true -> begin
(

let uu____564 = (aux ys iface_tl1)
in (match (uu____564) with
| (val_ys, iface3) -> begin
(((iface_hd1)::val_ys), (iface3))
end))
end
| uu____595 -> begin
(

let uu____596 = (

let uu____597 = (FStar_List.tryFind (is_val y.FStar_Ident.ident) iface_tl1)
in (FStar_All.pipe_left FStar_Option.isSome uu____597))
in (match (uu____596) with
| true -> begin
(

let uu____610 = (

let uu____615 = (

let uu____616 = (FStar_Parser_AST.decl_to_string iface_hd1)
in (

let uu____617 = (FStar_Ident.string_of_lid y)
in (FStar_Util.format2 "%s is out of order with the definition of %s" uu____616 uu____617)))
in ((FStar_Errors.Fatal_WrongDefinitionOrder), (uu____615)))
in (FStar_Errors.raise_error uu____610 iface_hd1.FStar_Parser_AST.drange))
end
| uu____626 -> begin
(aux ys iface2)
end))
end)
end))
in (

let uu____627 = (aux mutually_defined_with_x iface_tl)
in (match (uu____627) with
| (take_iface, rest_iface) -> begin
((rest_iface), ((FStar_List.append ((iface_hd)::take_iface) ((impl)::[]))))
end))))
end)))
end
| uu____658 -> begin
(

let uu____659 = (prefix_with_iface_decls iface_tl impl)
in (match (uu____659) with
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
| FStar_Parser_AST.Tycon (uu____715, tys) when (FStar_All.pipe_right tys (FStar_Util.for_some (fun uu___61_750 -> (match (uu___61_750) with
| (FStar_Parser_AST.TyconAbstract (uu____757), uu____758) -> begin
true
end
| uu____773 -> begin
false
end)))) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AbstractTypeDeclarationInInterface), ("Interface contains an abstract \'type\' declaration; use \'val\' instead")) hd1.FStar_Parser_AST.drange)
end
| FStar_Parser_AST.Val (x, t) -> begin
(

let uu____782 = (FStar_Util.for_some (is_definition_of x) tl1)
in (match (uu____782) with
| true -> begin
(

let uu____783 = (

let uu____788 = (FStar_Util.format2 "\'val %s\' and \'let %s\' cannot both be provided in an interface" x.FStar_Ident.idText x.FStar_Ident.idText)
in ((FStar_Errors.Fatal_BothValAndLetInInterface), (uu____788)))
in (FStar_Errors.raise_error uu____783 hd1.FStar_Parser_AST.drange))
end
| uu____789 -> begin
(

let uu____790 = (FStar_All.pipe_right hd1.FStar_Parser_AST.quals (FStar_List.contains FStar_Parser_AST.Assumption))
in (match (uu____790) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_AssumeValInInterface), ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead")) hd1.FStar_Parser_AST.drange)
end
| uu____793 -> begin
()
end))
end))
end
| uu____794 -> begin
()
end)
end))
in ((aux iface1);
(FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____803) -> begin
false
end
| uu____804 -> begin
true
end))));
)))


let rec ml_mode_prefix_with_iface_decls : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelLet (uu____835, defs) -> begin
(

let xs = (FStar_Parser_AST.lids_of_let defs)
in (

let uu____852 = (FStar_List.partition (fun d -> (FStar_All.pipe_right xs (FStar_Util.for_some (fun x -> (is_val x.FStar_Ident.ident d))))) iface1)
in (match (uu____852) with
| (val_xs, rest_iface) -> begin
((rest_iface), ((FStar_List.append val_xs ((impl)::[]))))
end)))
end
| uu____889 -> begin
((iface1), ((impl)::[]))
end))


let ml_mode_check_initial_interface : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list = (fun iface1 -> (FStar_All.pipe_right iface1 (FStar_List.filter (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (uu____912) -> begin
true
end
| uu____917 -> begin
false
end)))))


let prefix_one_decl : FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl  ->  (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list) = (fun iface1 impl -> (match (impl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____948) -> begin
((iface1), ((impl)::[]))
end
| uu____953 -> begin
(

let uu____954 = (FStar_Options.ml_ish ())
in (match (uu____954) with
| true -> begin
(ml_mode_prefix_with_iface_decls iface1 impl)
end
| uu____963 -> begin
(prefix_with_iface_decls iface1 impl)
end))
end))


let initialize_interface : FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  unit FStar_Syntax_DsEnv.withenv = (fun mname l env -> (

let decls = (

let uu____992 = (FStar_Options.ml_ish ())
in (match (uu____992) with
| true -> begin
(ml_mode_check_initial_interface l)
end
| uu____995 -> begin
(check_initial_interface l)
end))
in (

let uu____996 = (FStar_Syntax_DsEnv.iface_decls env mname)
in (match (uu____996) with
| FStar_Pervasives_Native.Some (uu____1005) -> begin
(

let uu____1010 = (

let uu____1015 = (

let uu____1016 = (FStar_Ident.string_of_lid mname)
in (FStar_Util.format1 "Interface %s has already been processed" uu____1016))
in ((FStar_Errors.Fatal_InterfaceAlreadyProcessed), (uu____1015)))
in (

let uu____1017 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____1010 uu____1017)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1024 = (FStar_Syntax_DsEnv.set_iface_decls env mname decls)
in ((()), (uu____1024)))
end))))


let prefix_with_interface_decls : FStar_Parser_AST.decl  ->  FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv = (fun impl env -> (

let uu____1045 = (

let uu____1050 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Syntax_DsEnv.iface_decls env uu____1050))
in (match (uu____1045) with
| FStar_Pervasives_Native.None -> begin
(((impl)::[]), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1066 = (prefix_one_decl iface1 impl)
in (match (uu____1066) with
| (iface2, impl1) -> begin
(

let env1 = (

let uu____1092 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Syntax_DsEnv.set_iface_decls env uu____1092 iface2))
in ((impl1), (env1)))
end))
end)))


let interleave_module : FStar_Parser_AST.modul  ->  Prims.bool  ->  FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv = (fun a expect_complete_modul env -> (match (a) with
| FStar_Parser_AST.Interface (uu____1120) -> begin
((a), (env))
end
| FStar_Parser_AST.Module (l, impls) -> begin
(

let uu____1135 = (FStar_Syntax_DsEnv.iface_decls env l)
in (match (uu____1135) with
| FStar_Pervasives_Native.None -> begin
((a), (env))
end
| FStar_Pervasives_Native.Some (iface1) -> begin
(

let uu____1151 = (FStar_List.fold_left (fun uu____1175 impl -> (match (uu____1175) with
| (iface2, impls1) -> begin
(

let uu____1203 = (prefix_one_decl iface2 impl)
in (match (uu____1203) with
| (iface3, impls') -> begin
((iface3), ((FStar_List.append impls1 impls')))
end))
end)) ((iface1), ([])) impls)
in (match (uu____1151) with
| (iface2, impls1) -> begin
(

let uu____1252 = (

let uu____1261 = (FStar_Util.prefix_until (fun uu___62_1280 -> (match (uu___62_1280) with
| {FStar_Parser_AST.d = FStar_Parser_AST.Val (uu____1281); FStar_Parser_AST.drange = uu____1282; FStar_Parser_AST.doc = uu____1283; FStar_Parser_AST.quals = uu____1284; FStar_Parser_AST.attrs = uu____1285} -> begin
true
end
| uu____1292 -> begin
false
end)) iface2)
in (match (uu____1261) with
| FStar_Pervasives_Native.None -> begin
((iface2), ([]))
end
| FStar_Pervasives_Native.Some (lets, one_val, rest) -> begin
((lets), ((one_val)::rest))
end))
in (match (uu____1252) with
| (iface_lets, remaining_iface_vals) -> begin
(

let impls2 = (FStar_List.append impls1 iface_lets)
in (

let env1 = (FStar_Syntax_DsEnv.set_iface_decls env l remaining_iface_vals)
in (

let a1 = FStar_Parser_AST.Module (((l), (impls2)))
in (match (remaining_iface_vals) with
| (uu____1365)::uu____1366 when expect_complete_modul -> begin
(

let err = (

let uu____1370 = (FStar_List.map FStar_Parser_AST.decl_to_string remaining_iface_vals)
in (FStar_All.pipe_right uu____1370 (FStar_String.concat "\n\t")))
in (

let uu____1375 = (

let uu____1380 = (

let uu____1381 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format2 "Some interface elements were not implemented by module %s:\n\t%s" uu____1381 err))
in ((FStar_Errors.Fatal_InterfaceNotImplementedByModule), (uu____1380)))
in (

let uu____1382 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____1375 uu____1382))))
end
| uu____1387 -> begin
((a1), (env1))
end))))
end))
end))
end))
end))




