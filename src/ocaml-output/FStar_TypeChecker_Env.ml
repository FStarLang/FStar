
open Prims
type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____29 -> begin
false
end))


let __proj__Binding_var__item___0 : binding  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
_0
end))


let uu___is_Binding_lid : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
true
end
| uu____43 -> begin
false
end))


let __proj__Binding_lid__item___0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
_0
end))


let uu___is_Binding_sig : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_sig (_0) -> begin
true
end
| uu____64 -> begin
false
end))


let __proj__Binding_sig__item___0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_0) -> begin
_0
end))


let uu___is_Binding_univ : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
true
end
| uu____85 -> begin
false
end))


let __proj__Binding_univ__item___0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
_0
end))


let uu___is_Binding_sig_inst : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_0) -> begin
true
end
| uu____101 -> begin
false
end))


let __proj__Binding_sig_inst__item___0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_0) -> begin
_0
end))

type delta_level =
| NoDelta
| Inlining
| Eager_unfolding_only
| Unfold of FStar_Syntax_Syntax.delta_depth


let uu___is_NoDelta : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDelta -> begin
true
end
| uu____127 -> begin
false
end))


let uu___is_Inlining : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____131 -> begin
false
end))


let uu___is_Eager_unfolding_only : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding_only -> begin
true
end
| uu____135 -> begin
false
end))


let uu___is_Unfold : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
true
end
| uu____140 -> begin
false
end))


let __proj__Unfold__item___0 : delta_level  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
_0
end))

type mlift =
{mlift_wp : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ; mlift_term : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) Prims.option}

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}

type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


type cached_elt =
(((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either * FStar_Range.range)


type goal =
FStar_Syntax_Syntax.term

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) Prims.option} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; preprocess : env  ->  goal  ->  (env * goal) Prims.list; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list); implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}


type implicits =
(Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list


type env_t =
env


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let should_verify : env  ->  Prims.bool = (fun env -> (((not (env.lax)) && (not (env.admit))) && (FStar_Options.should_verify env.curmodule.FStar_Ident.str)))


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| ((NoDelta, _)) | ((Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) | ((Unfold (_), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) | ((Unfold (_), FStar_Syntax_Syntax.Visible_default)) -> begin
true
end
| (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____839 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun uu____849 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache = (fun uu____857 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (

let uu____896 = (new_gamma_cache ())
in (

let uu____898 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____896; modules = []; expected_typ = None; sigtab = uu____898; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____938 -> (

let uu____939 = (FStar_ST.read query_indices)
in (match (uu____939) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____953 -> begin
(

let uu____958 = (

let uu____963 = (

let uu____967 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____967))
in (

let uu____981 = (FStar_ST.read query_indices)
in (uu____963)::uu____981))
in (FStar_ST.write query_indices uu____958))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____1003 -> (

let uu____1004 = (FStar_ST.read query_indices)
in (match (uu____1004) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.write query_indices tl1)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____1040 -> (match (uu____1040) with
| (l, n1) -> begin
(

let uu____1045 = (FStar_ST.read query_indices)
in (match (uu____1045) with
| (hd1)::tl1 -> begin
(FStar_ST.write query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____1079 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____1089 -> (

let uu____1090 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____1090)))


let commit_query_index_mark : Prims.unit  ->  Prims.unit = (fun uu____1106 -> (

let uu____1107 = (FStar_ST.read query_indices)
in (match (uu____1107) with
| (hd1)::(uu____1119)::tl1 -> begin
(FStar_ST.write query_indices ((hd1)::tl1))
end
| uu____1146 -> begin
(failwith "Unmarked query index stack")
end)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____1160 = (

let uu____1162 = (FStar_ST.read stack)
in (env)::uu____1162)
in (FStar_ST.write stack uu____1160));
(

let uu___108_1170 = env
in (

let uu____1171 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____1173 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___108_1170.solver; range = uu___108_1170.range; curmodule = uu___108_1170.curmodule; gamma = uu___108_1170.gamma; gamma_cache = uu____1171; modules = uu___108_1170.modules; expected_typ = uu___108_1170.expected_typ; sigtab = uu____1173; is_pattern = uu___108_1170.is_pattern; instantiate_imp = uu___108_1170.instantiate_imp; effects = uu___108_1170.effects; generalize = uu___108_1170.generalize; letrecs = uu___108_1170.letrecs; top_level = uu___108_1170.top_level; check_uvars = uu___108_1170.check_uvars; use_eq = uu___108_1170.use_eq; is_iface = uu___108_1170.is_iface; admit = uu___108_1170.admit; lax = uu___108_1170.lax; lax_universes = uu___108_1170.lax_universes; type_of = uu___108_1170.type_of; universe_of = uu___108_1170.universe_of; use_bv_sorts = uu___108_1170.use_bv_sorts; qname_and_index = uu___108_1170.qname_and_index})));
))


let pop_stack : Prims.unit  ->  env = (fun uu____1177 -> (

let uu____1178 = (FStar_ST.read stack)
in (match (uu____1178) with
| (env)::tl1 -> begin
((FStar_ST.write stack tl1);
env;
)
end
| uu____1190 -> begin
(failwith "Impossible: Too many pops")
end)))


let cleanup_interactive : env  ->  Prims.unit = (fun env -> (env.solver.pop ""))


let push : env  ->  Prims.string  ->  env = (fun env msg -> ((push_query_indices ());
(env.solver.push msg);
(push_stack env);
))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> ((env.solver.pop msg);
(pop_query_indices ());
(pop_stack ());
))


let mark : env  ->  env = (fun env -> ((env.solver.mark "USER MARK");
(push_query_indices ());
(push_stack env);
))


let commit_mark : env  ->  env = (fun env -> ((commit_query_index_mark ());
(env.solver.commit_mark "USER MARK");
(

let uu____1222 = (pop_stack ())
in ());
env;
))


let reset_mark : env  ->  env = (fun env -> ((env.solver.reset_mark "USER MARK");
(pop_query_indices ());
(pop_stack ());
))


let incr_query_index : env  ->  env = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n1) -> begin
(

let uu____1241 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____1253 -> (match (uu____1253) with
| (m, uu____1257) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____1241) with
| None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___109_1262 = env
in {solver = uu___109_1262.solver; range = uu___109_1262.range; curmodule = uu___109_1262.curmodule; gamma = uu___109_1262.gamma; gamma_cache = uu___109_1262.gamma_cache; modules = uu___109_1262.modules; expected_typ = uu___109_1262.expected_typ; sigtab = uu___109_1262.sigtab; is_pattern = uu___109_1262.is_pattern; instantiate_imp = uu___109_1262.instantiate_imp; effects = uu___109_1262.effects; generalize = uu___109_1262.generalize; letrecs = uu___109_1262.letrecs; top_level = uu___109_1262.top_level; check_uvars = uu___109_1262.check_uvars; use_eq = uu___109_1262.use_eq; is_iface = uu___109_1262.is_iface; admit = uu___109_1262.admit; lax = uu___109_1262.lax; lax_universes = uu___109_1262.lax_universes; type_of = uu___109_1262.type_of; universe_of = uu___109_1262.universe_of; use_bv_sorts = uu___109_1262.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end
| Some (uu____1265, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___110_1271 = env
in {solver = uu___110_1271.solver; range = uu___110_1271.range; curmodule = uu___110_1271.curmodule; gamma = uu___110_1271.gamma; gamma_cache = uu___110_1271.gamma_cache; modules = uu___110_1271.modules; expected_typ = uu___110_1271.expected_typ; sigtab = uu___110_1271.sigtab; is_pattern = uu___110_1271.is_pattern; instantiate_imp = uu___110_1271.instantiate_imp; effects = uu___110_1271.effects; generalize = uu___110_1271.generalize; letrecs = uu___110_1271.letrecs; top_level = uu___110_1271.top_level; check_uvars = uu___110_1271.check_uvars; use_eq = uu___110_1271.use_eq; is_iface = uu___110_1271.is_iface; admit = uu___110_1271.admit; lax = uu___110_1271.lax; lax_universes = uu___110_1271.lax_universes; type_of = uu___110_1271.type_of; universe_of = uu___110_1271.universe_of; use_bv_sorts = uu___110_1271.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((r = FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____1286 -> begin
(

let uu___111_1287 = e
in {solver = uu___111_1287.solver; range = r; curmodule = uu___111_1287.curmodule; gamma = uu___111_1287.gamma; gamma_cache = uu___111_1287.gamma_cache; modules = uu___111_1287.modules; expected_typ = uu___111_1287.expected_typ; sigtab = uu___111_1287.sigtab; is_pattern = uu___111_1287.is_pattern; instantiate_imp = uu___111_1287.instantiate_imp; effects = uu___111_1287.effects; generalize = uu___111_1287.generalize; letrecs = uu___111_1287.letrecs; top_level = uu___111_1287.top_level; check_uvars = uu___111_1287.check_uvars; use_eq = uu___111_1287.use_eq; is_iface = uu___111_1287.is_iface; admit = uu___111_1287.admit; lax = uu___111_1287.lax; lax_universes = uu___111_1287.lax_universes; type_of = uu___111_1287.type_of; universe_of = uu___111_1287.universe_of; use_bv_sorts = uu___111_1287.use_bv_sorts; qname_and_index = uu___111_1287.qname_and_index})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___112_1304 = env
in {solver = uu___112_1304.solver; range = uu___112_1304.range; curmodule = lid; gamma = uu___112_1304.gamma; gamma_cache = uu___112_1304.gamma_cache; modules = uu___112_1304.modules; expected_typ = uu___112_1304.expected_typ; sigtab = uu___112_1304.sigtab; is_pattern = uu___112_1304.is_pattern; instantiate_imp = uu___112_1304.instantiate_imp; effects = uu___112_1304.effects; generalize = uu___112_1304.generalize; letrecs = uu___112_1304.letrecs; top_level = uu___112_1304.top_level; check_uvars = uu___112_1304.check_uvars; use_eq = uu___112_1304.use_eq; is_iface = uu___112_1304.is_iface; admit = uu___112_1304.admit; lax = uu___112_1304.lax; lax_universes = uu___112_1304.lax_universes; type_of = uu___112_1304.type_of; universe_of = uu___112_1304.universe_of; use_bv_sorts = uu___112_1304.use_bv_sorts; qname_and_index = uu___112_1304.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v1 -> (

let uu____1326 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____1326)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____1329 -> (

let uu____1330 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1330)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____1353) -> begin
(

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))
in (

let uu____1369 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____1369)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___96_1374 -> (match (uu___96_1374) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____1388 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____1398 = (inst_tscheme t)
in (match (uu____1398) with
| (us, t1) -> begin
(

let uu____1405 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____1405)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____1417 -> (match (uu____1417) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs1 = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs1))) with
| true -> begin
(

let uu____1431 = (

let uu____1432 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (

let uu____1435 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____1438 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1439 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____1432 uu____1435 uu____1438 uu____1439)))))
in (failwith uu____1431))
end
| uu____1440 -> begin
()
end);
(

let uu____1441 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd uu____1441));
))
end
| uu____1445 -> begin
(

let uu____1446 = (

let uu____1447 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____1447))
in (failwith uu____1446))
end)
end))

type tri =
| Yes
| No
| Maybe


let uu___is_Yes : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Yes -> begin
true
end
| uu____1451 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____1455 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____1459 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____1467 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____1485) -> begin
Maybe
end
| (uu____1489, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (hd1.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____1501 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____1506 -> begin
No
end)
end)))


let lookup_qname : env  ->  FStar_Ident.lident  ->  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either * FStar_Range.range) Prims.option = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let cache = (fun t -> ((FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t);
Some (t);
))
in (

let found = (match ((cur_mod <> No)) with
| true -> begin
(

let uu____1561 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____1561) with
| None -> begin
(FStar_Util.find_map env.gamma (fun uu___97_1582 -> (match (uu___97_1582) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____1605 = (

let uu____1615 = (

let uu____1623 = (inst_tscheme t)
in FStar_Util.Inl (uu____1623))
in ((uu____1615), ((FStar_Ident.range_of_lid l))))
in Some (uu____1605))
end
| uu____1647 -> begin
None
end)
end
| Binding_sig (uu____1657, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____1659, uu____1660); FStar_Syntax_Syntax.sigdoc = uu____1661; FStar_Syntax_Syntax.sigrng = uu____1662}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____1673 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1673) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____1689 -> begin
None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1700) -> begin
Some (t)
end
| uu____1706 -> begin
(cache t)
end))
in (

let uu____1707 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____1707) with
| None -> begin
None
end
| Some (l) -> begin
(maybe_cache ((FStar_Util.Inr (((s), (None)))), ((FStar_Ident.range_of_lid l))))
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____1747 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____1747) with
| None -> begin
None
end
| Some (l) -> begin
Some (((FStar_Util.Inr (((s), (Some (us))))), ((FStar_Ident.range_of_lid l))))
end))
end
| uu____1791 -> begin
None
end)))
end
| se -> begin
se
end))
end
| uu____1803 -> begin
None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____1832 -> begin
(

let uu____1833 = ((cur_mod <> Yes) || (has_interface env env.curmodule))
in (match (uu____1833) with
| true -> begin
(

let uu____1844 = (find_in_sigtab env lid)
in (match (uu____1844) with
| Some (se) -> begin
Some (((FStar_Util.Inr (((se), (None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| None -> begin
None
end))
end
| uu____1888 -> begin
None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1910, uu____1911) -> begin
(add_sigelts env ses)
end
| uu____1918 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____1927 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___98_1945 -> (match (uu___98_1945) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (((id.FStar_Syntax_Syntax.sort), (id.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____1958 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) Prims.option = (fun se lid -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1979, (lb)::[]), uu____1981, uu____1982, uu____1983) -> begin
(

let uu____1994 = (

let uu____1999 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____2005 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____1999), (uu____2005))))
in Some (uu____1994))
end
| FStar_Syntax_Syntax.Sig_let ((uu____2012, lbs), uu____2014, uu____2015, uu____2016) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____2038) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____2045 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____2045) with
| true -> begin
(

let uu____2051 = (

let uu____2056 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____2062 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____2056), (uu____2062))))
in Some (uu____2051))
end
| uu____2069 -> begin
None
end))
end)))
end
| uu____2074 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) Prims.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____2093 = (

let uu____2098 = (

let uu____2101 = (

let uu____2102 = (

let uu____2105 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____2105))
in ((ne.FStar_Syntax_Syntax.univs), (uu____2102)))
in (inst_tscheme uu____2101))
in ((uu____2098), (se.FStar_Syntax_Syntax.sigrng)))
in Some (uu____2093))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____2119, uu____2120, uu____2121) -> begin
(

let uu____2126 = (

let uu____2131 = (

let uu____2134 = (

let uu____2135 = (

let uu____2138 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____2138))
in ((us), (uu____2135)))
in (inst_tscheme uu____2134))
in ((uu____2131), (se.FStar_Syntax_Syntax.sigrng)))
in Some (uu____2126))
end
| uu____2149 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) * FStar_Range.range) Prims.option = (fun env lid -> (

let mapper = (fun uu____2184 -> (match (uu____2184) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____2234, uvs, t, uu____2237, uu____2238, uu____2239, uu____2240); FStar_Syntax_Syntax.sigdoc = uu____2241; FStar_Syntax_Syntax.sigrng = uu____2242}, None) -> begin
(

let uu____2254 = (

let uu____2259 = (inst_tscheme ((uvs), (t)))
in ((uu____2259), (rng)))
in Some (uu____2254))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs); FStar_Syntax_Syntax.sigdoc = uu____2272; FStar_Syntax_Syntax.sigrng = uu____2273}, None) -> begin
(

let uu____2283 = (

let uu____2284 = (in_cur_mod env l)
in (uu____2284 = Yes))
in (match (uu____2283) with
| true -> begin
(

let uu____2290 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____2290) with
| true -> begin
(

let uu____2297 = (

let uu____2302 = (inst_tscheme ((uvs), (t)))
in ((uu____2302), (rng)))
in Some (uu____2297))
end
| uu____2311 -> begin
None
end))
end
| uu____2316 -> begin
(

let uu____2317 = (

let uu____2322 = (inst_tscheme ((uvs), (t)))
in ((uu____2322), (rng)))
in Some (uu____2317))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____2335, uu____2336, uu____2337); FStar_Syntax_Syntax.sigdoc = uu____2338; FStar_Syntax_Syntax.sigrng = uu____2339}, None) -> begin
(match (tps) with
| [] -> begin
(

let uu____2360 = (

let uu____2365 = (inst_tscheme ((uvs), (k)))
in ((uu____2365), (rng)))
in Some (uu____2360))
end
| uu____2374 -> begin
(

let uu____2375 = (

let uu____2380 = (

let uu____2383 = (

let uu____2384 = (

let uu____2387 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2387))
in ((uvs), (uu____2384)))
in (inst_tscheme uu____2383))
in ((uu____2380), (rng)))
in Some (uu____2375))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____2402, uu____2403, uu____2404); FStar_Syntax_Syntax.sigdoc = uu____2405; FStar_Syntax_Syntax.sigrng = uu____2406}, Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____2428 = (

let uu____2433 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____2433), (rng)))
in Some (uu____2428))
end
| uu____2442 -> begin
(

let uu____2443 = (

let uu____2448 = (

let uu____2451 = (

let uu____2452 = (

let uu____2455 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2455))
in ((uvs), (uu____2452)))
in (inst_tscheme_with uu____2451 us))
in ((uu____2448), (rng)))
in Some (uu____2443))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____2480); FStar_Syntax_Syntax.sigdoc = uu____2481; FStar_Syntax_Syntax.sigrng = uu____2482}, None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| uu____2493 -> begin
(effect_signature (Prims.fst se))
end)
end)
end))
in (

let uu____2498 = (

let uu____2504 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____2504 mapper))
in (match (uu____2498) with
| Some ((us, t), r) -> begin
Some (((((us), ((

let uu___113_2556 = t
in {FStar_Syntax_Syntax.n = uu___113_2556.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___113_2556.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___113_2556.FStar_Syntax_Syntax.vars})))), (r)))
end
| None -> begin
None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____2577 = (lookup_qname env l)
in (match (uu____2577) with
| None -> begin
false
end
| Some (uu____2597) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____2625 = (try_lookup_bv env bv)
in (match (uu____2625) with
| None -> begin
(

let uu____2633 = (

let uu____2634 = (

let uu____2637 = (variable_not_found bv)
in ((uu____2637), (bvr)))
in FStar_Errors.Error (uu____2634))
in (Prims.raise uu____2633))
end
| Some (t, r) -> begin
(

let uu____2644 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____2645 = (FStar_Range.set_use_range r bvr)
in ((uu____2644), (uu____2645))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) Prims.option = (fun env l -> (

let uu____2657 = (try_lookup_lid_aux env l)
in (match (uu____2657) with
| None -> begin
None
end
| Some ((us, t), r) -> begin
(

let use_range = (FStar_Ident.range_of_lid l)
in (

let r1 = (FStar_Range.set_use_range r use_range)
in (

let uu____2699 = (

let uu____2704 = (

let uu____2707 = (FStar_Syntax_Subst.set_use_range use_range t)
in ((us), (uu____2707)))
in ((uu____2704), (r1)))
in Some (uu____2699))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____2724 = (try_lookup_lid env l)
in (match (uu____2724) with
| None -> begin
(

let uu____2738 = (

let uu____2739 = (

let uu____2742 = (name_not_found l)
in ((uu____2742), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____2739))
in (Prims.raise uu____2738))
end
| Some ((us, t), r) -> begin
((((us), (t))), (r))
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___99_2765 -> (match (uu___99_2765) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____2767 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (

let uu____2778 = (lookup_qname env lid)
in (match (uu____2778) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____2793, uvs, t, q); FStar_Syntax_Syntax.sigdoc = uu____2797; FStar_Syntax_Syntax.sigrng = uu____2798}, None), uu____2799) -> begin
(

let uu____2825 = (

let uu____2831 = (

let uu____2834 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____2834)))
in ((uu____2831), (q)))
in Some (uu____2825))
end
| uu____2843 -> begin
None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2865 = (lookup_qname env lid)
in (match (uu____2865) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____2878, uvs, t, uu____2881); FStar_Syntax_Syntax.sigdoc = uu____2882; FStar_Syntax_Syntax.sigrng = uu____2883}, None), uu____2884) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2910 -> begin
(

let uu____2921 = (

let uu____2922 = (

let uu____2925 = (name_not_found lid)
in ((uu____2925), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2922))
in (Prims.raise uu____2921))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2936 = (lookup_qname env lid)
in (match (uu____2936) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____2949, uvs, t, uu____2952, uu____2953, uu____2954, uu____2955); FStar_Syntax_Syntax.sigdoc = uu____2956; FStar_Syntax_Syntax.sigrng = uu____2957}, None), uu____2958) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2986 -> begin
(

let uu____2997 = (

let uu____2998 = (

let uu____3001 = (name_not_found lid)
in ((uu____3001), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2998))
in (Prims.raise uu____2997))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____3013 = (lookup_qname env lid)
in (match (uu____3013) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____3027, uu____3028, uu____3029, uu____3030, uu____3031, dcs, uu____3033); FStar_Syntax_Syntax.sigdoc = uu____3034; FStar_Syntax_Syntax.sigrng = uu____3035}, uu____3036), uu____3037) -> begin
((true), (dcs))
end
| uu____3069 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____3087 = (lookup_qname env lid)
in (match (uu____3087) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____3098, uu____3099, uu____3100, l, uu____3102, uu____3103, uu____3104); FStar_Syntax_Syntax.sigdoc = uu____3105; FStar_Syntax_Syntax.sigrng = uu____3106}, uu____3107), uu____3108) -> begin
l
end
| uu____3137 -> begin
(

let uu____3148 = (

let uu____3149 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____3149))
in (failwith uu____3148))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____3173 = (lookup_qname env lid)
in (match (uu____3173) with
| Some (FStar_Util.Inr (se, None), uu____3188) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____3214, lbs), uu____3216, quals, uu____3218) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____3235 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____3235) with
| true -> begin
(

let uu____3240 = (

let uu____3244 = (

let uu____3245 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) uu____3245))
in ((lb.FStar_Syntax_Syntax.lbunivs), (uu____3244)))
in Some (uu____3240))
end
| uu____3250 -> begin
None
end)))))
end
| uu____3254 -> begin
None
end)
end
| uu____3257 -> begin
None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (

let uu____3278 = (lookup_qname env ftv)
in (match (uu____3278) with
| Some (FStar_Util.Inr (se, None), uu____3291) -> begin
(

let uu____3314 = (effect_signature se)
in (match (uu____3314) with
| None -> begin
None
end
| Some ((uu____3325, t), r) -> begin
(

let uu____3334 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (uu____3334))
end))
end
| uu____3335 -> begin
None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____3352 = (try_lookup_effect_lid env ftv)
in (match (uu____3352) with
| None -> begin
(

let uu____3354 = (

let uu____3355 = (

let uu____3358 = (name_not_found ftv)
in ((uu____3358), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____3355))
in (Prims.raise uu____3354))
end
| Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (

let uu____3372 = (lookup_qname env lid0)
in (match (uu____3372) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, quals, uu____3391); FStar_Syntax_Syntax.sigdoc = uu____3392; FStar_Syntax_Syntax.sigrng = uu____3393}, None), uu____3394) -> begin
(

let lid1 = (

let uu____3423 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____3423))
in (

let uu____3424 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___100_3426 -> (match (uu___100_3426) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____3427 -> begin
false
end))))
in (match (uu____3424) with
| true -> begin
None
end
| uu____3433 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____3439 -> begin
(match (((FStar_Ident.lid_equals lid1 FStar_Syntax_Const.effect_Lemma_lid) && ((FStar_List.length univ_insts) = (Prims.parse_int "1")))) with
| true -> begin
(FStar_List.append univ_insts ((FStar_Syntax_Syntax.U_zero)::[]))
end
| uu____3442 -> begin
(

let uu____3443 = (

let uu____3444 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____3445 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" uu____3444 uu____3445)))
in (failwith uu____3443))
end)
end)
in (match (((binders), (univs1))) with
| ([], uu____3451) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____3460, (uu____3461)::(uu____3462)::uu____3463) when (not ((FStar_Ident.lid_equals lid1 FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(

let uu____3466 = (

let uu____3467 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____3468 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____3467 uu____3468)))
in (failwith uu____3466))
end
| uu____3474 -> begin
(

let uu____3477 = (

let uu____3480 = (

let uu____3481 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____3481)))
in (inst_tscheme_with uu____3480 insts))
in (match (uu____3477) with
| (uu____3489, t) -> begin
(

let t1 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid1) t)
in (

let uu____3492 = (

let uu____3493 = (FStar_Syntax_Subst.compress t1)
in uu____3493.FStar_Syntax_Syntax.n)
in (match (uu____3492) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
Some (((binders1), (c1)))
end
| uu____3523 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____3527 -> begin
None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____3553 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____3553) with
| None -> begin
None
end
| Some (uu____3560, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____3565 = (find1 l2)
in (match (uu____3565) with
| None -> begin
Some (l2)
end
| Some (l') -> begin
Some (l')
end)))
end)))
in (

let res = (

let uu____3570 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____3570) with
| Some (l1) -> begin
l1
end
| None -> begin
(

let uu____3573 = (find1 l)
in (match (uu____3573) with
| None -> begin
l
end
| Some (m) -> begin
((FStar_Util.smap_add cache l.FStar_Ident.str m);
m;
)
end))
end))
in (FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l))))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l1 = (norm_eff_name env l)
in (

let uu____3585 = (lookup_qname env l1)
in (match (uu____3585) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigdoc = uu____3598; FStar_Syntax_Syntax.sigrng = uu____3599}, uu____3600), uu____3601) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| uu____3626 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____3649 -> (

let uu____3650 = (

let uu____3651 = (FStar_Util.string_of_int i)
in (

let uu____3652 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____3651 uu____3652)))
in (failwith uu____3650)))
in (

let uu____3653 = (lookup_datacon env lid)
in (match (uu____3653) with
| (uu____3656, t) -> begin
(

let uu____3658 = (

let uu____3659 = (FStar_Syntax_Subst.compress t)
in uu____3659.FStar_Syntax_Syntax.n)
in (match (uu____3658) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____3663) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____3678 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____3684 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right uu____3684 Prims.fst)))
end)
end
| uu____3689 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____3696 = (lookup_qname env l)
in (match (uu____3696) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____3707, uu____3708, uu____3709, quals); FStar_Syntax_Syntax.sigdoc = uu____3711; FStar_Syntax_Syntax.sigrng = uu____3712}, uu____3713), uu____3714) -> begin
(FStar_Util.for_some (fun uu___101_3741 -> (match (uu___101_3741) with
| FStar_Syntax_Syntax.Projector (uu____3742) -> begin
true
end
| uu____3745 -> begin
false
end)) quals)
end
| uu____3746 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3763 = (lookup_qname env lid)
in (match (uu____3763) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____3774, uu____3775, uu____3776, uu____3777, uu____3778, uu____3779, uu____3780); FStar_Syntax_Syntax.sigdoc = uu____3781; FStar_Syntax_Syntax.sigrng = uu____3782}, uu____3783), uu____3784) -> begin
true
end
| uu____3813 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3830 = (lookup_qname env lid)
in (match (uu____3830) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____3841, uu____3842, uu____3843, uu____3844, uu____3845, uu____3846, tags); FStar_Syntax_Syntax.sigdoc = uu____3848; FStar_Syntax_Syntax.sigrng = uu____3849}, uu____3850), uu____3851) -> begin
(FStar_Util.for_some (fun uu___102_3882 -> (match (uu___102_3882) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3885 -> begin
false
end)) tags)
end
| uu____3886 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3903 = (lookup_qname env lid)
in (match (uu____3903) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____3914, uu____3915, tags, uu____3917); FStar_Syntax_Syntax.sigdoc = uu____3918; FStar_Syntax_Syntax.sigrng = uu____3919}, uu____3920), uu____3921) -> begin
(FStar_Util.for_some (fun uu___103_3952 -> (match (uu___103_3952) with
| FStar_Syntax_Syntax.Action (uu____3953) -> begin
true
end
| uu____3954 -> begin
false
end)) tags)
end
| uu____3955 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____3974 = (

let uu____3975 = (FStar_Syntax_Util.un_uinst head1)
in uu____3975.FStar_Syntax_Syntax.n)
in (match (uu____3974) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____3979 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (uu____4017) -> begin
Some (false)
end
| FStar_Util.Inr (se, uu____4026) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4035, uu____4036, uu____4037, qs) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4041) -> begin
Some (true)
end
| uu____4052 -> begin
Some (false)
end)
end))
in (

let uu____4053 = (

let uu____4055 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____4055 mapper))
in (match (uu____4053) with
| Some (b) -> begin
b
end
| None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____4082 = (lookup_qname env lid)
in (match (uu____4082) with
| Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____4093, uu____4094, tps, uu____4096, uu____4097, uu____4098, uu____4099); FStar_Syntax_Syntax.sigdoc = uu____4100; FStar_Syntax_Syntax.sigrng = uu____4101}, uu____4102), uu____4103) -> begin
(FStar_List.length tps)
end
| uu____4137 -> begin
(

let uu____4148 = (

let uu____4149 = (

let uu____4152 = (name_not_found lid)
in ((uu____4152), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____4149))
in (Prims.raise uu____4148))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____4169 = (effect_decl_opt env l)
in (match (uu____4169) with
| None -> begin
(

let uu____4171 = (

let uu____4172 = (

let uu____4175 = (name_not_found l)
in ((uu____4175), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____4172))
in (Prims.raise uu____4171))
end
| Some (md) -> begin
md
end)))


let identity_mlift : mlift = {mlift_wp = (fun t wp -> wp); mlift_term = Some ((fun t wp e -> e))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____4206 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Syntax_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____4210 -> begin
(

let uu____4211 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____4235 -> (match (uu____4235) with
| (m1, m2, uu____4243, uu____4244, uu____4245) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____4211) with
| None -> begin
(

let uu____4254 = (

let uu____4255 = (

let uu____4258 = (

let uu____4259 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____4260 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____4259 uu____4260)))
in ((uu____4258), (env.range)))
in FStar_Errors.Error (uu____4255))
in (Prims.raise uu____4254))
end
| Some (uu____4264, uu____4265, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)))) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____4286 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____4302 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))
in (match (uu____4302) with
| None -> begin
(

let uu____4311 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____4311))
end
| Some (md) -> begin
(

let uu____4317 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____4317) with
| (uu____4324, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____4332))::((wp, uu____4334))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____4356 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (Some (res_u)))
end
| uu____4383 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (Some (res_u)))
end
| uu____4384 -> begin
(

let eff_name1 = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name1)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____4391 = (get_range env)
in (

let uu____4392 = (

let uu____4395 = (

let uu____4396 = (

let uu____4406 = (

let uu____4408 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____4408)::[])
in ((null_wp), (uu____4406)))
in FStar_Syntax_Syntax.Tm_app (uu____4396))
in (FStar_Syntax_Syntax.mk uu____4395))
in (uu____4392 None uu____4391)))
in (

let uu____4418 = (

let uu____4419 = (

let uu____4425 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____4425)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name1; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____4419; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____4418))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let effects = (

let uu___114_4434 = env.effects
in {decls = (ne)::env.effects.decls; order = uu___114_4434.order; joins = uu___114_4434.joins})
in (

let uu___115_4435 = env
in {solver = uu___115_4435.solver; range = uu___115_4435.range; curmodule = uu___115_4435.curmodule; gamma = uu___115_4435.gamma; gamma_cache = uu___115_4435.gamma_cache; modules = uu___115_4435.modules; expected_typ = uu___115_4435.expected_typ; sigtab = uu___115_4435.sigtab; is_pattern = uu___115_4435.is_pattern; instantiate_imp = uu___115_4435.instantiate_imp; effects = effects; generalize = uu___115_4435.generalize; letrecs = uu___115_4435.letrecs; top_level = uu___115_4435.top_level; check_uvars = uu___115_4435.check_uvars; use_eq = uu___115_4435.use_eq; is_iface = uu___115_4435.is_iface; admit = uu___115_4435.admit; lax = uu___115_4435.lax; lax_universes = uu___115_4435.lax_universes; type_of = uu___115_4435.type_of; universe_of = uu___115_4435.universe_of; use_bv_sorts = uu___115_4435.use_bv_sorts; qname_and_index = uu___115_4435.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun r wp1 -> (

let uu____4452 = (e1.mlift.mlift_wp r wp1)
in (e2.mlift.mlift_wp r uu____4452)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (Some (l1), Some (l2)) -> begin
Some ((fun t wp e -> (

let uu____4531 = (e1.mlift.mlift_wp t wp)
in (

let uu____4532 = (l1 t wp e)
in (l2 t uu____4531 uu____4532)))))
end
| uu____4533 -> begin
None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t r wp1 -> (

let uu____4568 = (inst_tscheme lift_t)
in (match (uu____4568) with
| (uu____4573, lift_t1) -> begin
(

let uu____4575 = (

let uu____4578 = (

let uu____4579 = (

let uu____4589 = (

let uu____4591 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____4592 = (

let uu____4594 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____4594)::[])
in (uu____4591)::uu____4592))
in ((lift_t1), (uu____4589)))
in FStar_Syntax_Syntax.Tm_app (uu____4579))
in (FStar_Syntax_Syntax.mk uu____4578))
in (uu____4575 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_mlift_wp = (match (sub1.FStar_Syntax_Syntax.lift_wp) with
| Some (sub_lift_wp) -> begin
(mk_mlift_wp sub_lift_wp)
end
| None -> begin
(failwith "sub effect should\'ve been elaborated at this stage")
end)
in (

let mk_mlift_term = (fun lift_t r wp1 e -> (

let uu____4639 = (inst_tscheme lift_t)
in (match (uu____4639) with
| (uu____4644, lift_t1) -> begin
(

let uu____4646 = (

let uu____4649 = (

let uu____4650 = (

let uu____4660 = (

let uu____4662 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____4663 = (

let uu____4665 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____4666 = (

let uu____4668 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4668)::[])
in (uu____4665)::uu____4666))
in (uu____4662)::uu____4663))
in ((lift_t1), (uu____4660)))
in FStar_Syntax_Syntax.Tm_app (uu____4650))
in (FStar_Syntax_Syntax.mk uu____4649))
in (uu____4646 None e.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_mlift_term = (FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term)
in (

let edge = {msource = sub1.FStar_Syntax_Syntax.source; mtarget = sub1.FStar_Syntax_Syntax.target; mlift = {mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term}}
in (

let id_edge = (fun l -> {msource = sub1.FStar_Syntax_Syntax.source; mtarget = sub1.FStar_Syntax_Syntax.target; mlift = identity_mlift})
in (

let print_mlift = (fun l -> (

let bogus_term = (fun s -> (

let uu____4709 = (

let uu____4710 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____4710 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.fv_to_tm uu____4709)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____4714 = (

let uu____4715 = (l.mlift_wp arg wp)
in (FStar_Syntax_Print.term_to_string uu____4715))
in (

let uu____4716 = (

let uu____4717 = (FStar_Util.map_opt l.mlift_term (fun l1 -> (

let uu____4732 = (l1 arg wp e)
in (FStar_Syntax_Print.term_to_string uu____4732))))
in (FStar_Util.dflt "none" uu____4717))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4714 uu____4716))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order1 uu____4750 -> (match (uu____4750) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_28 -> Some (_0_28)))
end
| uu____4759 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____4775 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____4781 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____4786 -> begin
(

let uu____4787 = (

let uu____4792 = (find_edge order1 ((i), (k)))
in (

let uu____4794 = (find_edge order1 ((k), (j)))
in ((uu____4792), (uu____4794))))
in (match (uu____4787) with
| (Some (e1), Some (e2)) -> begin
(

let uu____4803 = (compose_edges e1 e2)
in (uu____4803)::[])
end
| uu____4804 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order1 uu____4775)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____4819 = ((FStar_Ident.lid_equals edge1.msource FStar_Syntax_Const.effect_DIV_lid) && (

let uu____4820 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____4820 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____4819) with
| true -> begin
(

let uu____4823 = (

let uu____4824 = (

let uu____4827 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in (

let uu____4828 = (get_range env)
in ((uu____4827), (uu____4828))))
in FStar_Errors.Error (uu____4824))
in (Prims.raise uu____4823))
end
| uu____4829 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (match ((FStar_Ident.lid_equals i j)) with
| true -> begin
Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____4875 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____4891 = (

let uu____4896 = (find_edge order2 ((i), (k)))
in (

let uu____4898 = (find_edge order2 ((j), (k)))
in ((uu____4896), (uu____4898))))
in (match (uu____4891) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, uu____4921, uu____4922) -> begin
(

let uu____4926 = (

let uu____4929 = (

let uu____4930 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____4930))
in (

let uu____4932 = (

let uu____4933 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____4933))
in ((uu____4929), (uu____4932))))
in (match (uu____4926) with
| (true, true) -> begin
(match ((FStar_Ident.lid_equals k ub)) with
| true -> begin
((FStar_Util.print_warning "Looking multiple times at the same upper bound candidate");
bopt;
)
end
| uu____4944 -> begin
(failwith "Found a cycle in the lattice")
end)
end
| (false, false) -> begin
bopt
end
| (true, false) -> begin
Some (((k), (ik), (jk)))
end
| (false, true) -> begin
bopt
end))
end)
end
| uu____4952 -> begin
bopt
end))) None))
end)
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let uu___116_4991 = env.effects
in {decls = uu___116_4991.decls; order = order2; joins = joins})
in (

let uu___117_4992 = env
in {solver = uu___117_4992.solver; range = uu___117_4992.range; curmodule = uu___117_4992.curmodule; gamma = uu___117_4992.gamma; gamma_cache = uu___117_4992.gamma_cache; modules = uu___117_4992.modules; expected_typ = uu___117_4992.expected_typ; sigtab = uu___117_4992.sigtab; is_pattern = uu___117_4992.is_pattern; instantiate_imp = uu___117_4992.instantiate_imp; effects = effects; generalize = uu___117_4992.generalize; letrecs = uu___117_4992.letrecs; top_level = uu___117_4992.top_level; check_uvars = uu___117_4992.check_uvars; use_eq = uu___117_4992.use_eq; is_iface = uu___117_4992.is_iface; admit = uu___117_4992.admit; lax = uu___117_4992.lax; lax_universes = uu___117_4992.lax_universes; type_of = uu___117_4992.type_of; universe_of = uu___117_4992.universe_of; use_bv_sorts = uu___117_4992.use_bv_sorts; qname_and_index = uu___117_4992.qname_and_index})));
))))))))))))))
end
| uu____4993 -> begin
env
end))


let comp_to_comp_typ : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env c -> (

let c1 = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, None) -> begin
(

let u = (env.universe_of env t)
in (FStar_Syntax_Syntax.mk_Total' t (Some (u))))
end
| FStar_Syntax_Syntax.GTotal (t, None) -> begin
(

let u = (env.universe_of env t)
in (FStar_Syntax_Syntax.mk_GTotal' t (Some (u))))
end
| uu____5015 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____5023 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____5023) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let uu____5033 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____5033) with
| (binders1, cdef1) -> begin
((match (((FStar_List.length binders1) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____5050 = (

let uu____5051 = (

let uu____5054 = (

let uu____5055 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____5061 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____5069 = (

let uu____5070 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____5070))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____5055 uu____5061 uu____5069))))
in ((uu____5054), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____5051))
in (Prims.raise uu____5050))
end
| uu____5071 -> begin
()
end);
(

let inst1 = (

let uu____5074 = (

let uu____5080 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____5080)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____5087 uu____5088 -> (match (((uu____5087), (uu____5088))) with
| ((x, uu____5102), (t, uu____5104)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____5074))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____5119 = (

let uu___118_5120 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___118_5120.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___118_5120.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___118_5120.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___118_5120.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____5119 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux = (fun only_reifiable env c u_c -> (

let uu____5150 = (

let uu____5152 = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (effect_decl_opt env uu____5152))
in (match (uu____5150) with
| None -> begin
None
end
| Some (ed) -> begin
(

let uu____5159 = (only_reifiable && (

let uu____5160 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____5160))))
in (match (uu____5159) with
| true -> begin
None
end
| uu____5167 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
None
end
| uu____5173 -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let uu____5175 = (

let uu____5184 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in ((c1.FStar_Syntax_Syntax.result_typ), (uu____5184)))
in (match (uu____5175) with
| (res_typ, wp) -> begin
(

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____5218 = (

let uu____5221 = (get_range env)
in (

let uu____5222 = (

let uu____5225 = (

let uu____5226 = (

let uu____5236 = (

let uu____5238 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____5238)::(wp)::[])
in ((repr), (uu____5236)))
in FStar_Syntax_Syntax.Tm_app (uu____5226))
in (FStar_Syntax_Syntax.mk uu____5225))
in (uu____5222 None uu____5221)))
in Some (uu____5218)))
end)))
end)
end))
end)))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____5282 = (

let uu____5283 = (

let uu____5286 = (

let uu____5287 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____5287))
in (

let uu____5288 = (get_range env)
in ((uu____5286), (uu____5288))))
in FStar_Errors.Error (uu____5283))
in (Prims.raise uu____5282)))
in (

let uu____5289 = (effect_repr_aux true env c u_c)
in (match (uu____5289) with
| None -> begin
(no_reify (FStar_Syntax_Util.comp_effect_name c))
end
| Some (tm) -> begin
tm
end))))


let is_reifiable_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let quals = (lookup_effect_quals env effect_lid)
in (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals)))


let is_reifiable : env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either  ->  Prims.bool = (fun env c -> (

let effect_lid = (match (c) with
| FStar_Util.Inl (lc) -> begin
lc.FStar_Syntax_Syntax.eff_name
end
| FStar_Util.Inr (eff_name, uu____5321) -> begin
eff_name
end)
in (is_reifiable_effect env effect_lid)))


let is_reifiable_comp : env  ->  FStar_Syntax_Syntax.comp  ->  Prims.bool = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name)
end
| uu____5334 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____5341 = (

let uu____5342 = (FStar_Syntax_Subst.compress t)
in uu____5342.FStar_Syntax_Syntax.n)
in (match (uu____5341) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5345, c) -> begin
(is_reifiable_comp env c)
end
| uu____5357 -> begin
false
end)))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push1 = (fun x rest -> (match (rest) with
| ((Binding_sig (_))::_) | ((Binding_sig_inst (_))::_) -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest1 -> begin
(

let uu____5382 = (push1 x rest1)
in (local)::uu____5382)
end))
in (

let uu___119_5384 = env
in (

let uu____5385 = (push1 s env.gamma)
in {solver = uu___119_5384.solver; range = uu___119_5384.range; curmodule = uu___119_5384.curmodule; gamma = uu____5385; gamma_cache = uu___119_5384.gamma_cache; modules = uu___119_5384.modules; expected_typ = uu___119_5384.expected_typ; sigtab = uu___119_5384.sigtab; is_pattern = uu___119_5384.is_pattern; instantiate_imp = uu___119_5384.instantiate_imp; effects = uu___119_5384.effects; generalize = uu___119_5384.generalize; letrecs = uu___119_5384.letrecs; top_level = uu___119_5384.top_level; check_uvars = uu___119_5384.check_uvars; use_eq = uu___119_5384.use_eq; is_iface = uu___119_5384.is_iface; admit = uu___119_5384.admit; lax = uu___119_5384.lax; lax_universes = uu___119_5384.lax_universes; type_of = uu___119_5384.type_of; universe_of = uu___119_5384.universe_of; use_bv_sorts = uu___119_5384.use_bv_sorts; qname_and_index = uu___119_5384.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env1 = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env1 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env1 = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env1 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___120_5412 = env
in {solver = uu___120_5412.solver; range = uu___120_5412.range; curmodule = uu___120_5412.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___120_5412.gamma_cache; modules = uu___120_5412.modules; expected_typ = uu___120_5412.expected_typ; sigtab = uu___120_5412.sigtab; is_pattern = uu___120_5412.is_pattern; instantiate_imp = uu___120_5412.instantiate_imp; effects = uu___120_5412.effects; generalize = uu___120_5412.generalize; letrecs = uu___120_5412.letrecs; top_level = uu___120_5412.top_level; check_uvars = uu___120_5412.check_uvars; use_eq = uu___120_5412.use_eq; is_iface = uu___120_5412.is_iface; admit = uu___120_5412.admit; lax = uu___120_5412.lax; lax_universes = uu___120_5412.lax_universes; type_of = uu___120_5412.type_of; universe_of = uu___120_5412.universe_of; use_bv_sorts = uu___120_5412.use_bv_sorts; qname_and_index = uu___120_5412.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) Prims.option = (fun env -> (match (env.gamma) with
| (Binding_var (x))::rest -> begin
Some (((x), ((

let uu___121_5433 = env
in {solver = uu___121_5433.solver; range = uu___121_5433.range; curmodule = uu___121_5433.curmodule; gamma = rest; gamma_cache = uu___121_5433.gamma_cache; modules = uu___121_5433.modules; expected_typ = uu___121_5433.expected_typ; sigtab = uu___121_5433.sigtab; is_pattern = uu___121_5433.is_pattern; instantiate_imp = uu___121_5433.instantiate_imp; effects = uu___121_5433.effects; generalize = uu___121_5433.generalize; letrecs = uu___121_5433.letrecs; top_level = uu___121_5433.top_level; check_uvars = uu___121_5433.check_uvars; use_eq = uu___121_5433.use_eq; is_iface = uu___121_5433.is_iface; admit = uu___121_5433.admit; lax = uu___121_5433.lax; lax_universes = uu___121_5433.lax_universes; type_of = uu___121_5433.type_of; universe_of = uu___121_5433.universe_of; use_bv_sorts = uu___121_5433.use_bv_sorts; qname_and_index = uu___121_5433.qname_and_index}))))
end
| uu____5434 -> begin
None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____5447 -> (match (uu____5447) with
| (x, uu____5451) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___122_5471 = x1
in {FStar_Syntax_Syntax.ppname = uu___122_5471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_5471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___123_5501 = env
in {solver = uu___123_5501.solver; range = uu___123_5501.range; curmodule = uu___123_5501.curmodule; gamma = []; gamma_cache = uu___123_5501.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = uu___123_5501.sigtab; is_pattern = uu___123_5501.is_pattern; instantiate_imp = uu___123_5501.instantiate_imp; effects = uu___123_5501.effects; generalize = uu___123_5501.generalize; letrecs = uu___123_5501.letrecs; top_level = uu___123_5501.top_level; check_uvars = uu___123_5501.check_uvars; use_eq = uu___123_5501.use_eq; is_iface = uu___123_5501.is_iface; admit = uu___123_5501.admit; lax = uu___123_5501.lax; lax_universes = uu___123_5501.lax_universes; type_of = uu___123_5501.type_of; universe_of = uu___123_5501.universe_of; use_bv_sorts = uu___123_5501.use_bv_sorts; qname_and_index = uu___123_5501.qname_and_index});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___124_5516 = env
in {solver = uu___124_5516.solver; range = uu___124_5516.range; curmodule = uu___124_5516.curmodule; gamma = uu___124_5516.gamma; gamma_cache = uu___124_5516.gamma_cache; modules = uu___124_5516.modules; expected_typ = Some (t); sigtab = uu___124_5516.sigtab; is_pattern = uu___124_5516.is_pattern; instantiate_imp = uu___124_5516.instantiate_imp; effects = uu___124_5516.effects; generalize = uu___124_5516.generalize; letrecs = uu___124_5516.letrecs; top_level = uu___124_5516.top_level; check_uvars = uu___124_5516.check_uvars; use_eq = false; is_iface = uu___124_5516.is_iface; admit = uu___124_5516.admit; lax = uu___124_5516.lax; lax_universes = uu___124_5516.lax_universes; type_of = uu___124_5516.type_of; universe_of = uu___124_5516.universe_of; use_bv_sorts = uu___124_5516.use_bv_sorts; qname_and_index = uu___124_5516.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env_ -> (

let uu____5532 = (expected_typ env_)
in (((

let uu___125_5535 = env_
in {solver = uu___125_5535.solver; range = uu___125_5535.range; curmodule = uu___125_5535.curmodule; gamma = uu___125_5535.gamma; gamma_cache = uu___125_5535.gamma_cache; modules = uu___125_5535.modules; expected_typ = None; sigtab = uu___125_5535.sigtab; is_pattern = uu___125_5535.is_pattern; instantiate_imp = uu___125_5535.instantiate_imp; effects = uu___125_5535.effects; generalize = uu___125_5535.generalize; letrecs = uu___125_5535.letrecs; top_level = uu___125_5535.top_level; check_uvars = uu___125_5535.check_uvars; use_eq = false; is_iface = uu___125_5535.is_iface; admit = uu___125_5535.admit; lax = uu___125_5535.lax; lax_universes = uu___125_5535.lax_universes; type_of = uu___125_5535.type_of; universe_of = uu___125_5535.universe_of; use_bv_sorts = uu___125_5535.use_bv_sorts; qname_and_index = uu___125_5535.qname_and_index})), (uu____5532))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
(

let uu____5546 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___104_5550 -> (match (uu___104_5550) with
| Binding_sig (uu____5552, se) -> begin
(se)::[]
end
| uu____5556 -> begin
[]
end))))
in (FStar_All.pipe_right uu____5546 FStar_List.rev))
end
| uu____5559 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___126_5561 = env
in {solver = uu___126_5561.solver; range = uu___126_5561.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___126_5561.gamma_cache; modules = (m)::env.modules; expected_typ = uu___126_5561.expected_typ; sigtab = uu___126_5561.sigtab; is_pattern = uu___126_5561.is_pattern; instantiate_imp = uu___126_5561.instantiate_imp; effects = uu___126_5561.effects; generalize = uu___126_5561.generalize; letrecs = uu___126_5561.letrecs; top_level = uu___126_5561.top_level; check_uvars = uu___126_5561.check_uvars; use_eq = uu___126_5561.use_eq; is_iface = uu___126_5561.is_iface; admit = uu___126_5561.admit; lax = uu___126_5561.lax; lax_universes = uu___126_5561.lax_universes; type_of = uu___126_5561.type_of; universe_of = uu___126_5561.universe_of; use_bv_sorts = uu___126_5561.use_bv_sorts; qname_and_index = uu___126_5561.qname_and_index});
))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs1 = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (uu____5611))::tl1 -> begin
(aux out tl1)
end
| ((Binding_lid (_, (_, t)))::tl1) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl1) -> begin
(

let uu____5626 = (

let uu____5630 = (FStar_Syntax_Free.uvars t)
in (ext out uu____5630))
in (aux uu____5626 tl1))
end
| ((Binding_sig (_))::_) | ((Binding_sig_inst (_))::_) -> begin
out
end))
in (aux no_uvs1 env.gamma)))))


let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (

let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| ((Binding_sig_inst (_))::tl1) | ((Binding_univ (_))::tl1) -> begin
(aux out tl1)
end
| ((Binding_lid (_, (_, t)))::tl1) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl1) -> begin
(

let uu____5686 = (

let uu____5688 = (FStar_Syntax_Free.univs t)
in (ext out uu____5688))
in (aux uu____5686 tl1))
end
| (Binding_sig (uu____5690))::uu____5691 -> begin
out
end))
in (aux no_univs env.gamma)))))


let univnames : env  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun env -> (

let no_univ_names = FStar_Syntax_Syntax.no_universe_names
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (uu____5728))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uname))::tl1 -> begin
(

let uu____5738 = (FStar_Util.set_add uname out)
in (aux uu____5738 tl1))
end
| ((Binding_lid (_, (_, t)))::tl1) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl1) -> begin
(

let uu____5752 = (

let uu____5754 = (FStar_Syntax_Free.univnames t)
in (ext out uu____5754))
in (aux uu____5752 tl1))
end
| (Binding_sig (uu____5756))::uu____5757 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___105_5773 -> (match (uu___105_5773) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____5785 = (

let uu____5787 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____5787 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____5785 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : env  ->  Prims.unit = (fun env -> (

let uu____5803 = (

let uu____5804 = (FStar_All.pipe_right env.gamma (FStar_List.map (fun uu___106_5808 -> (match (uu___106_5808) with
| Binding_var (x) -> begin
(

let uu____5810 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____5810))
end
| Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| Binding_lid (l, uu____5813) -> begin
(

let uu____5814 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____5814))
end
| Binding_sig (ls, uu____5816) -> begin
(

let uu____5819 = (

let uu____5820 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____5820 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig " uu____5819))
end
| Binding_sig_inst (ls, uu____5826, uu____5827) -> begin
(

let uu____5830 = (

let uu____5831 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____5831 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig_inst " uu____5830))
end))))
in (FStar_All.pipe_right uu____5804 (FStar_String.concat "::\n")))
in (FStar_All.pipe_right uu____5803 (FStar_Util.print1 "%s\n"))))


let eq_gamma : env  ->  env  ->  Prims.bool = (fun env env' -> (

let uu____5843 = (FStar_Util.physical_equality env.gamma env'.gamma)
in (match (uu____5843) with
| true -> begin
true
end
| uu____5845 -> begin
(

let g = (all_binders env)
in (

let g' = (all_binders env')
in (((FStar_List.length g) = (FStar_List.length g')) && (FStar_List.forall2 (fun uu____5860 uu____5861 -> (match (((uu____5860), (uu____5861))) with
| ((b1, uu____5871), (b2, uu____5873)) -> begin
(FStar_Syntax_Syntax.bv_eq b1 b2)
end)) g g'))))
end)))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a1 -> (f a1 e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___107_5916 -> (match (uu___107_5916) with
| Binding_sig (lids, uu____5920) -> begin
(FStar_List.append lids keys)
end
| uu____5923 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____5925 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let dummy_solver : solver_t = {init = (fun uu____5929 -> ()); push = (fun uu____5930 -> ()); pop = (fun uu____5931 -> ()); mark = (fun uu____5932 -> ()); reset_mark = (fun uu____5933 -> ()); commit_mark = (fun uu____5934 -> ()); encode_modul = (fun uu____5935 uu____5936 -> ()); encode_sig = (fun uu____5937 uu____5938 -> ()); preprocess = (fun e g -> (((e), (g)))::[]); solve = (fun uu____5945 uu____5946 uu____5947 -> ()); is_trivial = (fun uu____5951 uu____5952 -> false); finish = (fun uu____5953 -> ()); refresh = (fun uu____5954 -> ())}




