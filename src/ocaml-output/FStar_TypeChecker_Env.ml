
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
FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ}

type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) Prims.option} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}


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
| uu____764 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun uu____774 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache = (fun uu____782 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (

let uu____821 = (new_gamma_cache ())
in (

let uu____823 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____821; modules = []; expected_typ = None; sigtab = uu____823; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)

type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun uu____948 -> (

let uu____949 = (FStar_ST.read query_indices)
in (match (uu____949) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____963 -> begin
(

let uu____968 = (

let uu____973 = (

let uu____977 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____977))
in (

let uu____991 = (FStar_ST.read query_indices)
in (uu____973)::uu____991))
in (FStar_ST.write query_indices uu____968))
end)))
in (

let pop_query_indices = (fun uu____1014 -> (

let uu____1015 = (FStar_ST.read query_indices)
in (match (uu____1015) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd)::tl -> begin
(FStar_ST.write query_indices tl)
end)))
in (

let add_query_index = (fun uu____1052 -> (match (uu____1052) with
| (l, n) -> begin
(

let uu____1057 = (FStar_ST.read query_indices)
in (match (uu____1057) with
| (hd)::tl -> begin
(FStar_ST.write query_indices (((((l), (n)))::hd)::tl))
end
| uu____1091 -> begin
(failwith "Empty query indices")
end))
end))
in (

let peek_query_indices = (fun uu____1102 -> (

let uu____1103 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____1103)))
in (

let commit_query_index_mark = (fun uu____1120 -> (

let uu____1121 = (FStar_ST.read query_indices)
in (match (uu____1121) with
| (hd)::(uu____1133)::tl -> begin
(FStar_ST.write query_indices ((hd)::tl))
end
| uu____1160 -> begin
(failwith "Unmarked query index stack")
end)))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> ((

let uu____1175 = (

let uu____1177 = (FStar_ST.read stack)
in (env)::uu____1177)
in (FStar_ST.write stack uu____1175));
(

let uu___105_1185 = env
in (

let uu____1186 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____1188 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___105_1185.solver; range = uu___105_1185.range; curmodule = uu___105_1185.curmodule; gamma = uu___105_1185.gamma; gamma_cache = uu____1186; modules = uu___105_1185.modules; expected_typ = uu___105_1185.expected_typ; sigtab = uu____1188; is_pattern = uu___105_1185.is_pattern; instantiate_imp = uu___105_1185.instantiate_imp; effects = uu___105_1185.effects; generalize = uu___105_1185.generalize; letrecs = uu___105_1185.letrecs; top_level = uu___105_1185.top_level; check_uvars = uu___105_1185.check_uvars; use_eq = uu___105_1185.use_eq; is_iface = uu___105_1185.is_iface; admit = uu___105_1185.admit; lax = uu___105_1185.lax; lax_universes = uu___105_1185.lax_universes; type_of = uu___105_1185.type_of; universe_of = uu___105_1185.universe_of; use_bv_sorts = uu___105_1185.use_bv_sorts; qname_and_index = uu___105_1185.qname_and_index})));
))
in (

let pop_stack = (fun env -> (

let uu____1194 = (FStar_ST.read stack)
in (match (uu____1194) with
| (env)::tl -> begin
((FStar_ST.write stack tl);
env;
)
end
| uu____1206 -> begin
(failwith "Impossible: Too many pops")
end)))
in (

let push = (fun env -> ((push_query_indices ());
(push_stack env);
))
in (

let pop = (fun env -> ((pop_query_indices ());
(pop_stack env);
))
in (

let mark = (fun env -> ((push_query_indices ());
(push_stack env);
))
in (

let commit_mark = (fun env -> ((commit_query_index_mark ());
(

let uu____1229 = (pop_stack env)
in ());
env;
))
in (

let reset_mark = (fun env -> ((pop_query_indices ());
(pop_stack env);
))
in (

let incr_query_index = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(

let uu____1249 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____1261 -> (match (uu____1261) with
| (m, uu____1265) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____1249) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___106_1270 = env
in {solver = uu___106_1270.solver; range = uu___106_1270.range; curmodule = uu___106_1270.curmodule; gamma = uu___106_1270.gamma; gamma_cache = uu___106_1270.gamma_cache; modules = uu___106_1270.modules; expected_typ = uu___106_1270.expected_typ; sigtab = uu___106_1270.sigtab; is_pattern = uu___106_1270.is_pattern; instantiate_imp = uu___106_1270.instantiate_imp; effects = uu___106_1270.effects; generalize = uu___106_1270.generalize; letrecs = uu___106_1270.letrecs; top_level = uu___106_1270.top_level; check_uvars = uu___106_1270.check_uvars; use_eq = uu___106_1270.use_eq; is_iface = uu___106_1270.is_iface; admit = uu___106_1270.admit; lax = uu___106_1270.lax; lax_universes = uu___106_1270.lax_universes; type_of = uu___106_1270.type_of; universe_of = uu___106_1270.universe_of; use_bv_sorts = uu___106_1270.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end
| Some (uu____1273, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___107_1279 = env
in {solver = uu___107_1279.solver; range = uu___107_1279.range; curmodule = uu___107_1279.curmodule; gamma = uu___107_1279.gamma; gamma_cache = uu___107_1279.gamma_cache; modules = uu___107_1279.modules; expected_typ = uu___107_1279.expected_typ; sigtab = uu___107_1279.sigtab; is_pattern = uu___107_1279.is_pattern; instantiate_imp = uu___107_1279.instantiate_imp; effects = uu___107_1279.effects; generalize = uu___107_1279.generalize; letrecs = uu___107_1279.letrecs; top_level = uu___107_1279.top_level; check_uvars = uu___107_1279.check_uvars; use_eq = uu___107_1279.use_eq; is_iface = uu___107_1279.is_iface; admit = uu___107_1279.admit; lax = uu___107_1279.lax; lax_universes = uu___107_1279.lax_universes; type_of = uu___107_1279.type_of; universe_of = uu___107_1279.universe_of; use_bv_sorts = uu___107_1279.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end))
end)))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop; es_incr_query_index = incr_query_index})))))))))))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> ((env.solver.push msg);
(stack_ops.es_push env);
))


let mark : env  ->  env = (fun env -> ((env.solver.mark "USER MARK");
(stack_ops.es_mark env);
))


let commit_mark : env  ->  env = (fun env -> ((env.solver.commit_mark "USER MARK");
(stack_ops.es_commit_mark env);
))


let reset_mark : env  ->  env = (fun env -> ((env.solver.reset_mark "USER MARK");
(stack_ops.es_reset_mark env);
))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> ((env.solver.pop msg);
(stack_ops.es_pop env);
))


let cleanup_interactive : env  ->  Prims.unit = (fun env -> (env.solver.pop ""))


let incr_query_index : env  ->  env = (fun env -> (stack_ops.es_incr_query_index env))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((r = FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____1326 -> begin
(

let uu___108_1327 = e
in {solver = uu___108_1327.solver; range = r; curmodule = uu___108_1327.curmodule; gamma = uu___108_1327.gamma; gamma_cache = uu___108_1327.gamma_cache; modules = uu___108_1327.modules; expected_typ = uu___108_1327.expected_typ; sigtab = uu___108_1327.sigtab; is_pattern = uu___108_1327.is_pattern; instantiate_imp = uu___108_1327.instantiate_imp; effects = uu___108_1327.effects; generalize = uu___108_1327.generalize; letrecs = uu___108_1327.letrecs; top_level = uu___108_1327.top_level; check_uvars = uu___108_1327.check_uvars; use_eq = uu___108_1327.use_eq; is_iface = uu___108_1327.is_iface; admit = uu___108_1327.admit; lax = uu___108_1327.lax; lax_universes = uu___108_1327.lax_universes; type_of = uu___108_1327.type_of; universe_of = uu___108_1327.universe_of; use_bv_sorts = uu___108_1327.use_bv_sorts; qname_and_index = uu___108_1327.qname_and_index})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___109_1344 = env
in {solver = uu___109_1344.solver; range = uu___109_1344.range; curmodule = lid; gamma = uu___109_1344.gamma; gamma_cache = uu___109_1344.gamma_cache; modules = uu___109_1344.modules; expected_typ = uu___109_1344.expected_typ; sigtab = uu___109_1344.sigtab; is_pattern = uu___109_1344.is_pattern; instantiate_imp = uu___109_1344.instantiate_imp; effects = uu___109_1344.effects; generalize = uu___109_1344.generalize; letrecs = uu___109_1344.letrecs; top_level = uu___109_1344.top_level; check_uvars = uu___109_1344.check_uvars; use_eq = uu___109_1344.use_eq; is_iface = uu___109_1344.is_iface; admit = uu___109_1344.admit; lax = uu___109_1344.lax; lax_universes = uu___109_1344.lax_universes; type_of = uu___109_1344.type_of; universe_of = uu___109_1344.universe_of; use_bv_sorts = uu___109_1344.use_bv_sorts; qname_and_index = uu___109_1344.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (

let uu____1366 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____1366)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____1369 -> (

let uu____1370 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1370)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____1393) -> begin
(

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (

let uu____1409 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____1409)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___92_1414 -> (match (uu___92_1414) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____1428 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____1438 = (inst_tscheme t)
in (match (uu____1438) with
| (us, t) -> begin
(

let uu____1445 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (uu____1445)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____1457 -> (match (uu____1457) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs))) with
| true -> begin
(

let uu____1471 = (

let uu____1472 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (

let uu____1475 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____1478 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1479 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____1472 uu____1475 uu____1478 uu____1479)))))
in (failwith uu____1471))
end
| uu____1480 -> begin
()
end);
(

let uu____1481 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd uu____1481));
))
end
| uu____1485 -> begin
(

let uu____1486 = (

let uu____1487 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____1487))
in (failwith uu____1486))
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
| uu____1491 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____1495 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____1499 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____1507 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match (((c), (l))) with
| ([], uu____1525) -> begin
Maybe
end
| (uu____1529, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| uu____1541 -> begin
No
end))
in (aux cur lns))))
end
| uu____1546 -> begin
No
end)
end)))


let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let cache = (fun t -> ((FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t);
Some (t);
))
in (

let found = (match ((cur_mod <> No)) with
| true -> begin
(

let uu____1593 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____1593) with
| None -> begin
(FStar_Util.find_map env.gamma (fun uu___93_1610 -> (match (uu___93_1610) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____1629 = (

let uu____1637 = (inst_tscheme t)
in FStar_Util.Inl (uu____1637))
in Some (uu____1629))
end
| uu____1652 -> begin
None
end)
end
| Binding_sig (uu____1660, FStar_Syntax_Syntax.Sig_bundle (ses, uu____1662, uu____1663, uu____1664)) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____1674 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1674) with
| true -> begin
(cache (FStar_Util.Inr (((se), (None)))))
end
| uu____1683 -> begin
None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1694) -> begin
Some (t)
end
| uu____1701 -> begin
(cache t)
end))
in (

let uu____1702 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1702) with
| true -> begin
(maybe_cache (FStar_Util.Inr (((s), (None)))))
end
| uu____1718 -> begin
None
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____1731 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1731) with
| true -> begin
Some (FStar_Util.Inr (((s), (Some (us)))))
end
| uu____1754 -> begin
None
end))
end
| uu____1762 -> begin
None
end)))
end
| se -> begin
se
end))
end
| uu____1772 -> begin
None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____1795 -> begin
(

let uu____1796 = ((cur_mod <> Yes) || (has_interface env env.curmodule))
in (match (uu____1796) with
| true -> begin
(

let uu____1805 = (find_in_sigtab env lid)
in (match (uu____1805) with
| Some (se) -> begin
Some (FStar_Util.Inr (((se), (None))))
end
| None -> begin
None
end))
end
| uu____1836 -> begin
None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1856, uu____1857, uu____1858) -> begin
(add_sigelts env ses)
end
| uu____1865 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1871) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____1875 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___94_1891 -> (match (uu___94_1891) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| uu____1898 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____1913, (lb)::[]), uu____1915, uu____1916, uu____1917, uu____1918) -> begin
(

let uu____1929 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (uu____1929))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1937, lbs), uu____1939, uu____1940, uu____1941, uu____1942) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1960) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____1965 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1965) with
| true -> begin
(

let uu____1969 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (uu____1969))
end
| uu____1977 -> begin
None
end))
end)))
end
| uu____1980 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1993) -> begin
(

let uu____1994 = (

let uu____1997 = (

let uu____1998 = (

let uu____2001 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____2001))
in ((ne.FStar_Syntax_Syntax.univs), (uu____1998)))
in (inst_tscheme uu____1997))
in Some (uu____1994))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____2011, uu____2012, uu____2013, uu____2014) -> begin
(

let uu____2019 = (

let uu____2022 = (

let uu____2023 = (

let uu____2026 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____2026))
in ((us), (uu____2023)))
in (inst_tscheme uu____2022))
in Some (uu____2019))
end
| uu____2033 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun uu___95_2060 -> (match (uu___95_2060) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2081, uvs, t, uu____2084, uu____2085, uu____2086, uu____2087, uu____2088), None) -> begin
(

let uu____2099 = (inst_tscheme ((uvs), (t)))
in Some (uu____2099))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, uu____2108), None) -> begin
(

let uu____2117 = (

let uu____2118 = (in_cur_mod env l)
in (uu____2118 = Yes))
in (match (uu____2117) with
| true -> begin
(

let uu____2122 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____2122) with
| true -> begin
(

let uu____2127 = (inst_tscheme ((uvs), (t)))
in Some (uu____2127))
end
| uu____2132 -> begin
None
end))
end
| uu____2135 -> begin
(

let uu____2136 = (inst_tscheme ((uvs), (t)))
in Some (uu____2136))
end))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2145, uu____2146, uu____2147, uu____2148), None) -> begin
(match (tps) with
| [] -> begin
(

let uu____2166 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _0_28 -> Some (_0_28)) uu____2166))
end
| uu____2176 -> begin
(

let uu____2177 = (

let uu____2180 = (

let uu____2181 = (

let uu____2184 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2184))
in ((uvs), (uu____2181)))
in (inst_tscheme uu____2180))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____2177))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2200, uu____2201, uu____2202, uu____2203), Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____2222 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____2222))
end
| uu____2232 -> begin
(

let uu____2233 = (

let uu____2236 = (

let uu____2237 = (

let uu____2240 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2240))
in ((uvs), (uu____2237)))
in (inst_tscheme_with uu____2236 us))
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____2233))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (uu____2264), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| uu____2275 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (

let uu____2280 = (

let uu____2284 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____2284 mapper))
in (match (uu____2280) with
| Some (us, t) -> begin
Some (((us), ((

let uu___110_2317 = t
in {FStar_Syntax_Syntax.n = uu___110_2317.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___110_2317.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___110_2317.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____2334 = (lookup_qname env l)
in (match (uu____2334) with
| None -> begin
false
end
| Some (uu____2350) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (

let uu____2371 = (try_lookup_bv env bv)
in (match (uu____2371) with
| None -> begin
(

let uu____2377 = (

let uu____2378 = (

let uu____2381 = (variable_not_found bv)
in (

let uu____2382 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____2381), (uu____2382))))
in FStar_Errors.Error (uu____2378))
in (Prims.raise uu____2377))
end
| Some (t) -> begin
(

let uu____2388 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range uu____2388 t))
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (

let uu____2398 = (try_lookup_lid_aux env l)
in (match (uu____2398) with
| None -> begin
None
end
| Some (us, t) -> begin
(

let uu____2423 = (

let uu____2426 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (uu____2426)))
in Some (uu____2423))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (

let uu____2437 = (try_lookup_lid env l)
in (match (uu____2437) with
| None -> begin
(

let uu____2445 = (

let uu____2446 = (

let uu____2449 = (name_not_found l)
in ((uu____2449), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____2446))
in (Prims.raise uu____2445))
end
| Some (us, t) -> begin
((us), (t))
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___96_2463 -> (match (uu___96_2463) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____2465 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (

let uu____2476 = (lookup_qname env lid)
in (match (uu____2476) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2489, uvs, t, q, uu____2493), None)) -> begin
(

let uu____2509 = (

let uu____2515 = (

let uu____2518 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____2518)))
in ((uu____2515), (q)))
in Some (uu____2509))
end
| uu____2527 -> begin
None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2547 = (lookup_qname env lid)
in (match (uu____2547) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2558, uvs, t, uu____2561, uu____2562), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2578 -> begin
(

let uu____2587 = (

let uu____2588 = (

let uu____2591 = (name_not_found lid)
in ((uu____2591), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2588))
in (Prims.raise uu____2587))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2602 = (lookup_qname env lid)
in (match (uu____2602) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2613, uvs, t, uu____2616, uu____2617, uu____2618, uu____2619, uu____2620), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2638 -> begin
(

let uu____2647 = (

let uu____2648 = (

let uu____2651 = (name_not_found lid)
in ((uu____2651), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2648))
in (Prims.raise uu____2647))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (

let uu____2661 = (lookup_qname env lid)
in (match (uu____2661) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____2671, uu____2672, uu____2673, uu____2674, uu____2675, dcs, uu____2677, uu____2678), uu____2679)) -> begin
dcs
end
| uu____2700 -> begin
[]
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____2715 = (lookup_qname env lid)
in (match (uu____2715) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2724, uu____2725, uu____2726, l, uu____2728, uu____2729, uu____2730, uu____2731), uu____2732)) -> begin
l
end
| uu____2751 -> begin
(

let uu____2760 = (

let uu____2761 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____2761))
in (failwith uu____2760))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____2785 = (lookup_qname env lid)
in (match (uu____2785) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____2814, lbs), uu____2816, uu____2817, quals, uu____2819) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2836 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____2836) with
| true -> begin
(

let uu____2841 = (

let uu____2845 = (

let uu____2846 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) uu____2846))
in ((lb.FStar_Syntax_Syntax.lbunivs), (uu____2845)))
in Some (uu____2841))
end
| uu____2851 -> begin
None
end)))))
end
| uu____2855 -> begin
None
end)
end
| uu____2858 -> begin
None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (

let uu____2877 = (lookup_qname env ftv)
in (match (uu____2877) with
| Some (FStar_Util.Inr (se, None)) -> begin
(

let uu____2901 = (effect_signature se)
in (match (uu____2901) with
| None -> begin
None
end
| Some (uu____2908, t) -> begin
(

let uu____2912 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (uu____2912))
end))
end
| uu____2913 -> begin
None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____2928 = (try_lookup_effect_lid env ftv)
in (match (uu____2928) with
| None -> begin
(

let uu____2930 = (

let uu____2931 = (

let uu____2934 = (name_not_found ftv)
in ((uu____2934), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____2931))
in (Prims.raise uu____2930))
end
| Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (

let uu____2948 = (lookup_qname env lid0)
in (match (uu____2948) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, uu____2965, uu____2966), None)) -> begin
(

let lid = (

let uu____2985 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____2985))
in (

let uu____2986 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___97_2988 -> (match (uu___97_2988) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____2989 -> begin
false
end))))
in (match (uu____2986) with
| true -> begin
None
end
| uu____2995 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs))) with
| true -> begin
univ_insts
end
| uu____3001 -> begin
(match (((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) && ((FStar_List.length univ_insts) = (Prims.parse_int "1")))) with
| true -> begin
(FStar_List.append univ_insts ((FStar_Syntax_Syntax.U_zero)::[]))
end
| uu____3004 -> begin
(

let uu____3005 = (

let uu____3006 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____3007 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" uu____3006 uu____3007)))
in (failwith uu____3005))
end)
end)
in (match (((binders), (univs))) with
| ([], uu____3013) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____3022, (uu____3023)::(uu____3024)::uu____3025) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(

let uu____3028 = (

let uu____3029 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____3030 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____3029 uu____3030)))
in (failwith uu____3028))
end
| uu____3036 -> begin
(

let uu____3039 = (

let uu____3042 = (

let uu____3043 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (uu____3043)))
in (inst_tscheme_with uu____3042 insts))
in (match (uu____3039) with
| (uu____3051, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (

let uu____3054 = (

let uu____3055 = (FStar_Syntax_Subst.compress t)
in uu____3055.FStar_Syntax_Syntax.n)
in (match (uu____3054) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| uu____3085 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____3089 -> begin
None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (

let uu____3113 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)
in (match (uu____3113) with
| None -> begin
None
end
| Some (uu____3120, c) -> begin
(

let l = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____3125 = (find l)
in (match (uu____3125) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end)))
end)))
in (

let res = (

let uu____3130 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____3130) with
| Some (l) -> begin
l
end
| None -> begin
(

let uu____3133 = (find l)
in (match (uu____3133) with
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

let l = (norm_eff_name env l)
in (

let uu____3145 = (lookup_qname env l)
in (match (uu____3145) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3156), uu____3157)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| uu____3172 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____3193 -> (

let uu____3194 = (

let uu____3195 = (FStar_Util.string_of_int i)
in (

let uu____3196 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____3195 uu____3196)))
in (failwith uu____3194)))
in (

let uu____3197 = (lookup_datacon env lid)
in (match (uu____3197) with
| (uu____3200, t) -> begin
(

let uu____3202 = (

let uu____3203 = (FStar_Syntax_Subst.compress t)
in uu____3203.FStar_Syntax_Syntax.n)
in (match (uu____3202) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____3207) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____3222 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____3228 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right uu____3228 Prims.fst)))
end)
end
| uu____3233 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____3240 = (lookup_qname env l)
in (match (uu____3240) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____3249, uu____3250, uu____3251, quals, uu____3253), uu____3254)) -> begin
(FStar_Util.for_some (fun uu___98_3271 -> (match (uu___98_3271) with
| FStar_Syntax_Syntax.Projector (uu____3272) -> begin
true
end
| uu____3275 -> begin
false
end)) quals)
end
| uu____3276 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3291 = (lookup_qname env lid)
in (match (uu____3291) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____3300, uu____3301, uu____3302, uu____3303, uu____3304, uu____3305, uu____3306, uu____3307), uu____3308)) -> begin
true
end
| uu____3327 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3342 = (lookup_qname env lid)
in (match (uu____3342) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3351, uu____3352, uu____3353, uu____3354, uu____3355, uu____3356, tags, uu____3358), uu____3359)) -> begin
(FStar_Util.for_some (fun uu___99_3380 -> (match (uu___99_3380) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3383 -> begin
false
end)) tags)
end
| uu____3384 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3399 = (lookup_qname env lid)
in (match (uu____3399) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_let (uu____3408, uu____3409, uu____3410, tags, uu____3412), uu____3413)) -> begin
(FStar_Util.for_some (fun uu___100_3434 -> (match (uu___100_3434) with
| FStar_Syntax_Syntax.Action (uu____3435) -> begin
true
end
| uu____3436 -> begin
false
end)) tags)
end
| uu____3437 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (

let uu____3454 = (

let uu____3455 = (FStar_Syntax_Util.un_uinst head)
in uu____3455.FStar_Syntax_Syntax.n)
in (match (uu____3454) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____3459 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun uu___101_3477 -> (match (uu___101_3477) with
| FStar_Util.Inl (uu____3486) -> begin
Some (false)
end
| FStar_Util.Inr (se, uu____3495) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____3504, uu____3505, uu____3506, qs, uu____3508) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3511) -> begin
Some (true)
end
| uu____3523 -> begin
Some (false)
end)
end))
in (

let uu____3524 = (

let uu____3526 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____3526 mapper))
in (match (uu____3524) with
| Some (b) -> begin
b
end
| None -> begin
false
end))))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____3559 = (effect_decl_opt env l)
in (match (uu____3559) with
| None -> begin
(

let uu____3561 = (

let uu____3562 = (

let uu____3565 = (name_not_found l)
in ((uu____3565), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3562))
in (Prims.raise uu____3561))
end
| Some (md) -> begin
md
end)))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3613 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3637 -> begin
(

let uu____3638 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____3662 -> (match (uu____3662) with
| (m1, m2, uu____3670, uu____3671, uu____3672) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____3638) with
| None -> begin
(

let uu____3689 = (

let uu____3690 = (

let uu____3693 = (

let uu____3694 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____3695 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____3694 uu____3695)))
in ((uu____3693), (env.range)))
in FStar_Errors.Error (uu____3690))
in (Prims.raise uu____3689))
end
| Some (uu____3707, uu____3708, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)))) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end
| uu____3739 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____3755 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))
in (match (uu____3755) with
| None -> begin
(

let uu____3764 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____3764))
end
| Some (md) -> begin
(

let uu____3770 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____3770) with
| (uu____3777, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____3785))::((wp, uu____3787))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____3809 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3831) -> begin
(

let effects = (

let uu___111_3833 = env.effects
in {decls = (ne)::env.effects.decls; order = uu___111_3833.order; joins = uu___111_3833.joins})
in (

let uu___112_3834 = env
in {solver = uu___112_3834.solver; range = uu___112_3834.range; curmodule = uu___112_3834.curmodule; gamma = uu___112_3834.gamma; gamma_cache = uu___112_3834.gamma_cache; modules = uu___112_3834.modules; expected_typ = uu___112_3834.expected_typ; sigtab = uu___112_3834.sigtab; is_pattern = uu___112_3834.is_pattern; instantiate_imp = uu___112_3834.instantiate_imp; effects = effects; generalize = uu___112_3834.generalize; letrecs = uu___112_3834.letrecs; top_level = uu___112_3834.top_level; check_uvars = uu___112_3834.check_uvars; use_eq = uu___112_3834.use_eq; is_iface = uu___112_3834.is_iface; admit = uu___112_3834.admit; lax = uu___112_3834.lax; lax_universes = uu___112_3834.lax_universes; type_of = uu___112_3834.type_of; universe_of = uu___112_3834.universe_of; use_bv_sorts = uu___112_3834.use_bv_sorts; qname_and_index = uu___112_3834.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, uu____3836) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (

let uu____3846 = (e1.mlift r wp1)
in (e2.mlift r uu____3846)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let uu____3859 = (inst_tscheme lift_t)
in (match (uu____3859) with
| (uu____3864, lift_t) -> begin
(

let uu____3866 = (

let uu____3869 = (

let uu____3870 = (

let uu____3880 = (

let uu____3882 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____3883 = (

let uu____3885 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____3885)::[])
in (uu____3882)::uu____3883))
in ((lift_t), (uu____3880)))
in FStar_Syntax_Syntax.Tm_app (uu____3870))
in (FStar_Syntax_Syntax.mk uu____3869))
in (uu____3866 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_lift_wp = (match (sub.FStar_Syntax_Syntax.lift_wp) with
| Some (sub_lift_wp) -> begin
sub_lift_wp
end
| None -> begin
(failwith "sub effect should\'ve been elaborated at this stage")
end)
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub_lift_wp)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (

let uu____3919 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____3919 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (

let uu____3921 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____3921 FStar_Syntax_Syntax.Delta_constant None))
in (

let uu____3922 = (l arg wp)
in (FStar_Syntax_Print.term_to_string uu____3922)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order uu____3940 -> (match (uu____3940) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_32 -> Some (_0_32)))
end
| uu____3949 -> begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (

let uu____3961 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____3967 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____3972 -> begin
(

let uu____3973 = (

let uu____3978 = (find_edge order ((i), (k)))
in (

let uu____3980 = (find_edge order ((k), (j)))
in ((uu____3978), (uu____3980))))
in (match (uu____3973) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| uu____3989 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order uu____3961))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in ((FStar_All.pipe_right order (FStar_List.iter (fun edge -> (

let uu____4001 = ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (

let uu____4002 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right uu____4002 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____4001) with
| true -> begin
(

let uu____4005 = (

let uu____4006 = (

let uu____4009 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (

let uu____4010 = (get_range env)
in ((uu____4009), (uu____4010))))
in FStar_Errors.Error (uu____4006))
in (Prims.raise uu____4005))
end
| uu____4011 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____4105 = (

let uu____4110 = (find_edge order ((i), (k)))
in (

let uu____4112 = (find_edge order ((j), (k)))
in ((uu____4110), (uu____4112))))
in (match (uu____4105) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, uu____4135, uu____4136) -> begin
(

let uu____4140 = ((

let uu____4141 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some uu____4141)) && (

let uu____4143 = (

let uu____4144 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some uu____4144))
in (not (uu____4143))))
in (match (uu____4140) with
| true -> begin
Some (((k), (ik), (jk)))
end
| uu____4153 -> begin
bopt
end))
end)
end
| uu____4154 -> begin
bopt
end))) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let uu___113_4233 = env.effects
in {decls = uu___113_4233.decls; order = order; joins = joins})
in (

let uu___114_4234 = env
in {solver = uu___114_4234.solver; range = uu___114_4234.range; curmodule = uu___114_4234.curmodule; gamma = uu___114_4234.gamma; gamma_cache = uu___114_4234.gamma_cache; modules = uu___114_4234.modules; expected_typ = uu___114_4234.expected_typ; sigtab = uu___114_4234.sigtab; is_pattern = uu___114_4234.is_pattern; instantiate_imp = uu___114_4234.instantiate_imp; effects = effects; generalize = uu___114_4234.generalize; letrecs = uu___114_4234.letrecs; top_level = uu___114_4234.top_level; check_uvars = uu___114_4234.check_uvars; use_eq = uu___114_4234.use_eq; is_iface = uu___114_4234.is_iface; admit = uu___114_4234.admit; lax = uu___114_4234.lax; lax_universes = uu___114_4234.lax_universes; type_of = uu___114_4234.type_of; universe_of = uu___114_4234.universe_of; use_bv_sorts = uu___114_4234.use_bv_sorts; qname_and_index = uu___114_4234.qname_and_index})));
))))))))))))
end
| uu____4235 -> begin
env
end))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push = (fun x rest -> (match (rest) with
| ((Binding_sig (_))::_) | ((Binding_sig_inst (_))::_) -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest -> begin
(

let uu____4260 = (push x rest)
in (local)::uu____4260)
end))
in (

let uu___115_4262 = env
in (

let uu____4263 = (push s env.gamma)
in {solver = uu___115_4262.solver; range = uu___115_4262.range; curmodule = uu___115_4262.curmodule; gamma = uu____4263; gamma_cache = uu___115_4262.gamma_cache; modules = uu___115_4262.modules; expected_typ = uu___115_4262.expected_typ; sigtab = uu___115_4262.sigtab; is_pattern = uu___115_4262.is_pattern; instantiate_imp = uu___115_4262.instantiate_imp; effects = uu___115_4262.effects; generalize = uu___115_4262.generalize; letrecs = uu___115_4262.letrecs; top_level = uu___115_4262.top_level; check_uvars = uu___115_4262.check_uvars; use_eq = uu___115_4262.use_eq; is_iface = uu___115_4262.is_iface; admit = uu___115_4262.admit; lax = uu___115_4262.lax; lax_universes = uu___115_4262.lax_universes; type_of = uu___115_4262.type_of; universe_of = uu___115_4262.universe_of; use_bv_sorts = uu___115_4262.use_bv_sorts; qname_and_index = uu___115_4262.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___116_4290 = env
in {solver = uu___116_4290.solver; range = uu___116_4290.range; curmodule = uu___116_4290.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___116_4290.gamma_cache; modules = uu___116_4290.modules; expected_typ = uu___116_4290.expected_typ; sigtab = uu___116_4290.sigtab; is_pattern = uu___116_4290.is_pattern; instantiate_imp = uu___116_4290.instantiate_imp; effects = uu___116_4290.effects; generalize = uu___116_4290.generalize; letrecs = uu___116_4290.letrecs; top_level = uu___116_4290.top_level; check_uvars = uu___116_4290.check_uvars; use_eq = uu___116_4290.use_eq; is_iface = uu___116_4290.is_iface; admit = uu___116_4290.admit; lax = uu___116_4290.lax; lax_universes = uu___116_4290.lax_universes; type_of = uu___116_4290.type_of; universe_of = uu___116_4290.universe_of; use_bv_sorts = uu___116_4290.use_bv_sorts; qname_and_index = uu___116_4290.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env uu____4306 -> (match (uu____4306) with
| (x, uu____4310) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let x = (

let uu___117_4330 = x
in {FStar_Syntax_Syntax.ppname = uu___117_4330.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_4330.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___118_4360 = env
in {solver = uu___118_4360.solver; range = uu___118_4360.range; curmodule = uu___118_4360.curmodule; gamma = []; gamma_cache = uu___118_4360.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = uu___118_4360.sigtab; is_pattern = uu___118_4360.is_pattern; instantiate_imp = uu___118_4360.instantiate_imp; effects = uu___118_4360.effects; generalize = uu___118_4360.generalize; letrecs = uu___118_4360.letrecs; top_level = uu___118_4360.top_level; check_uvars = uu___118_4360.check_uvars; use_eq = uu___118_4360.use_eq; is_iface = uu___118_4360.is_iface; admit = uu___118_4360.admit; lax = uu___118_4360.lax; lax_universes = uu___118_4360.lax_universes; type_of = uu___118_4360.type_of; universe_of = uu___118_4360.universe_of; use_bv_sorts = uu___118_4360.use_bv_sorts; qname_and_index = uu___118_4360.qname_and_index});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___119_4375 = env
in {solver = uu___119_4375.solver; range = uu___119_4375.range; curmodule = uu___119_4375.curmodule; gamma = uu___119_4375.gamma; gamma_cache = uu___119_4375.gamma_cache; modules = uu___119_4375.modules; expected_typ = Some (t); sigtab = uu___119_4375.sigtab; is_pattern = uu___119_4375.is_pattern; instantiate_imp = uu___119_4375.instantiate_imp; effects = uu___119_4375.effects; generalize = uu___119_4375.generalize; letrecs = uu___119_4375.letrecs; top_level = uu___119_4375.top_level; check_uvars = uu___119_4375.check_uvars; use_eq = false; is_iface = uu___119_4375.is_iface; admit = uu___119_4375.admit; lax = uu___119_4375.lax; lax_universes = uu___119_4375.lax_universes; type_of = uu___119_4375.type_of; universe_of = uu___119_4375.universe_of; use_bv_sorts = uu___119_4375.use_bv_sorts; qname_and_index = uu___119_4375.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (

let uu____4388 = (expected_typ env)
in (((

let uu___120_4391 = env
in {solver = uu___120_4391.solver; range = uu___120_4391.range; curmodule = uu___120_4391.curmodule; gamma = uu___120_4391.gamma; gamma_cache = uu___120_4391.gamma_cache; modules = uu___120_4391.modules; expected_typ = None; sigtab = uu___120_4391.sigtab; is_pattern = uu___120_4391.is_pattern; instantiate_imp = uu___120_4391.instantiate_imp; effects = uu___120_4391.effects; generalize = uu___120_4391.generalize; letrecs = uu___120_4391.letrecs; top_level = uu___120_4391.top_level; check_uvars = uu___120_4391.check_uvars; use_eq = false; is_iface = uu___120_4391.is_iface; admit = uu___120_4391.admit; lax = uu___120_4391.lax; lax_universes = uu___120_4391.lax_universes; type_of = uu___120_4391.type_of; universe_of = uu___120_4391.universe_of; use_bv_sorts = uu___120_4391.use_bv_sorts; qname_and_index = uu___120_4391.qname_and_index})), (uu____4388))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
(

let uu____4402 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___102_4406 -> (match (uu___102_4406) with
| Binding_sig (uu____4408, se) -> begin
(se)::[]
end
| uu____4412 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4402 FStar_List.rev))
end
| uu____4415 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___121_4417 = env
in {solver = uu___121_4417.solver; range = uu___121_4417.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___121_4417.gamma_cache; modules = (m)::env.modules; expected_typ = uu___121_4417.expected_typ; sigtab = uu___121_4417.sigtab; is_pattern = uu___121_4417.is_pattern; instantiate_imp = uu___121_4417.instantiate_imp; effects = uu___121_4417.effects; generalize = uu___121_4417.generalize; letrecs = uu___121_4417.letrecs; top_level = uu___121_4417.top_level; check_uvars = uu___121_4417.check_uvars; use_eq = uu___121_4417.use_eq; is_iface = uu___121_4417.is_iface; admit = uu___121_4417.admit; lax = uu___121_4417.lax; lax_universes = uu___121_4417.lax_universes; type_of = uu___121_4417.type_of; universe_of = uu___121_4417.universe_of; use_bv_sorts = uu___121_4417.use_bv_sorts; qname_and_index = uu___121_4417.qname_and_index});
))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (uu____4467))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4482 = (

let uu____4486 = (FStar_Syntax_Free.uvars t)
in (ext out uu____4486))
in (aux uu____4482 tl))
end
| ((Binding_sig (_))::_) | ((Binding_sig_inst (_))::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))


let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (

let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| ((Binding_sig_inst (_))::tl) | ((Binding_univ (_))::tl) -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4542 = (

let uu____4544 = (FStar_Syntax_Free.univs t)
in (ext out uu____4544))
in (aux uu____4542 tl))
end
| (Binding_sig (uu____4546))::uu____4547 -> begin
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
| (Binding_sig_inst (uu____4584))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(

let uu____4594 = (FStar_Util.set_add uname out)
in (aux uu____4594 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4608 = (

let uu____4610 = (FStar_Syntax_Free.univnames t)
in (ext out uu____4610))
in (aux uu____4608 tl))
end
| (Binding_sig (uu____4612))::uu____4613 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___103_4629 -> (match (uu___103_4629) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____4641 = (

let uu____4643 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____4643 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____4641 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___104_4694 -> (match (uu___104_4694) with
| Binding_sig (lids, uu____4698) -> begin
(FStar_List.append lids keys)
end
| uu____4701 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____4703 v keys -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)) keys)))


let dummy_solver : solver_t = {init = (fun uu____4707 -> ()); push = (fun uu____4708 -> ()); pop = (fun uu____4709 -> ()); mark = (fun uu____4710 -> ()); reset_mark = (fun uu____4711 -> ()); commit_mark = (fun uu____4712 -> ()); encode_modul = (fun uu____4713 uu____4714 -> ()); encode_sig = (fun uu____4715 uu____4716 -> ()); solve = (fun uu____4717 uu____4718 uu____4719 -> ()); is_trivial = (fun uu____4723 uu____4724 -> false); finish = (fun uu____4725 -> ()); refresh = (fun uu____4726 -> ())}




