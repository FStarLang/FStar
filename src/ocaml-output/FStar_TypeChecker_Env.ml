
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
| uu____773 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun uu____783 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache = (fun uu____791 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (

let uu____830 = (new_gamma_cache ())
in (

let uu____832 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____830; modules = []; expected_typ = None; sigtab = uu____832; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)

type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun uu____957 -> (

let uu____958 = (FStar_ST.read query_indices)
in (match (uu____958) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____972 -> begin
(

let uu____977 = (

let uu____982 = (

let uu____986 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____986))
in (

let uu____1000 = (FStar_ST.read query_indices)
in (uu____982)::uu____1000))
in (FStar_ST.write query_indices uu____977))
end)))
in (

let pop_query_indices = (fun uu____1023 -> (

let uu____1024 = (FStar_ST.read query_indices)
in (match (uu____1024) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd)::tl -> begin
(FStar_ST.write query_indices tl)
end)))
in (

let add_query_index = (fun uu____1061 -> (match (uu____1061) with
| (l, n) -> begin
(

let uu____1066 = (FStar_ST.read query_indices)
in (match (uu____1066) with
| (hd)::tl -> begin
(FStar_ST.write query_indices (((((l), (n)))::hd)::tl))
end
| uu____1100 -> begin
(failwith "Empty query indices")
end))
end))
in (

let peek_query_indices = (fun uu____1111 -> (

let uu____1112 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____1112)))
in (

let commit_query_index_mark = (fun uu____1129 -> (

let uu____1130 = (FStar_ST.read query_indices)
in (match (uu____1130) with
| (hd)::(uu____1142)::tl -> begin
(FStar_ST.write query_indices ((hd)::tl))
end
| uu____1169 -> begin
(failwith "Unmarked query index stack")
end)))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> ((

let uu____1184 = (

let uu____1186 = (FStar_ST.read stack)
in (env)::uu____1186)
in (FStar_ST.write stack uu____1184));
(

let uu___106_1194 = env
in (

let uu____1195 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____1197 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___106_1194.solver; range = uu___106_1194.range; curmodule = uu___106_1194.curmodule; gamma = uu___106_1194.gamma; gamma_cache = uu____1195; modules = uu___106_1194.modules; expected_typ = uu___106_1194.expected_typ; sigtab = uu____1197; is_pattern = uu___106_1194.is_pattern; instantiate_imp = uu___106_1194.instantiate_imp; effects = uu___106_1194.effects; generalize = uu___106_1194.generalize; letrecs = uu___106_1194.letrecs; top_level = uu___106_1194.top_level; check_uvars = uu___106_1194.check_uvars; use_eq = uu___106_1194.use_eq; is_iface = uu___106_1194.is_iface; admit = uu___106_1194.admit; lax = uu___106_1194.lax; lax_universes = uu___106_1194.lax_universes; type_of = uu___106_1194.type_of; universe_of = uu___106_1194.universe_of; use_bv_sorts = uu___106_1194.use_bv_sorts; qname_and_index = uu___106_1194.qname_and_index})));
))
in (

let pop_stack = (fun env -> (

let uu____1203 = (FStar_ST.read stack)
in (match (uu____1203) with
| (env)::tl -> begin
((FStar_ST.write stack tl);
env;
)
end
| uu____1215 -> begin
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

let uu____1238 = (pop_stack env)
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

let uu____1258 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____1270 -> (match (uu____1270) with
| (m, uu____1274) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____1258) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___107_1279 = env
in {solver = uu___107_1279.solver; range = uu___107_1279.range; curmodule = uu___107_1279.curmodule; gamma = uu___107_1279.gamma; gamma_cache = uu___107_1279.gamma_cache; modules = uu___107_1279.modules; expected_typ = uu___107_1279.expected_typ; sigtab = uu___107_1279.sigtab; is_pattern = uu___107_1279.is_pattern; instantiate_imp = uu___107_1279.instantiate_imp; effects = uu___107_1279.effects; generalize = uu___107_1279.generalize; letrecs = uu___107_1279.letrecs; top_level = uu___107_1279.top_level; check_uvars = uu___107_1279.check_uvars; use_eq = uu___107_1279.use_eq; is_iface = uu___107_1279.is_iface; admit = uu___107_1279.admit; lax = uu___107_1279.lax; lax_universes = uu___107_1279.lax_universes; type_of = uu___107_1279.type_of; universe_of = uu___107_1279.universe_of; use_bv_sorts = uu___107_1279.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end
| Some (uu____1282, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___108_1288 = env
in {solver = uu___108_1288.solver; range = uu___108_1288.range; curmodule = uu___108_1288.curmodule; gamma = uu___108_1288.gamma; gamma_cache = uu___108_1288.gamma_cache; modules = uu___108_1288.modules; expected_typ = uu___108_1288.expected_typ; sigtab = uu___108_1288.sigtab; is_pattern = uu___108_1288.is_pattern; instantiate_imp = uu___108_1288.instantiate_imp; effects = uu___108_1288.effects; generalize = uu___108_1288.generalize; letrecs = uu___108_1288.letrecs; top_level = uu___108_1288.top_level; check_uvars = uu___108_1288.check_uvars; use_eq = uu___108_1288.use_eq; is_iface = uu___108_1288.is_iface; admit = uu___108_1288.admit; lax = uu___108_1288.lax; lax_universes = uu___108_1288.lax_universes; type_of = uu___108_1288.type_of; universe_of = uu___108_1288.universe_of; use_bv_sorts = uu___108_1288.use_bv_sorts; qname_and_index = Some (((l), (next)))});
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
| uu____1335 -> begin
(

let uu___109_1336 = e
in {solver = uu___109_1336.solver; range = r; curmodule = uu___109_1336.curmodule; gamma = uu___109_1336.gamma; gamma_cache = uu___109_1336.gamma_cache; modules = uu___109_1336.modules; expected_typ = uu___109_1336.expected_typ; sigtab = uu___109_1336.sigtab; is_pattern = uu___109_1336.is_pattern; instantiate_imp = uu___109_1336.instantiate_imp; effects = uu___109_1336.effects; generalize = uu___109_1336.generalize; letrecs = uu___109_1336.letrecs; top_level = uu___109_1336.top_level; check_uvars = uu___109_1336.check_uvars; use_eq = uu___109_1336.use_eq; is_iface = uu___109_1336.is_iface; admit = uu___109_1336.admit; lax = uu___109_1336.lax; lax_universes = uu___109_1336.lax_universes; type_of = uu___109_1336.type_of; universe_of = uu___109_1336.universe_of; use_bv_sorts = uu___109_1336.use_bv_sorts; qname_and_index = uu___109_1336.qname_and_index})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___110_1353 = env
in {solver = uu___110_1353.solver; range = uu___110_1353.range; curmodule = lid; gamma = uu___110_1353.gamma; gamma_cache = uu___110_1353.gamma_cache; modules = uu___110_1353.modules; expected_typ = uu___110_1353.expected_typ; sigtab = uu___110_1353.sigtab; is_pattern = uu___110_1353.is_pattern; instantiate_imp = uu___110_1353.instantiate_imp; effects = uu___110_1353.effects; generalize = uu___110_1353.generalize; letrecs = uu___110_1353.letrecs; top_level = uu___110_1353.top_level; check_uvars = uu___110_1353.check_uvars; use_eq = uu___110_1353.use_eq; is_iface = uu___110_1353.is_iface; admit = uu___110_1353.admit; lax = uu___110_1353.lax; lax_universes = uu___110_1353.lax_universes; type_of = uu___110_1353.type_of; universe_of = uu___110_1353.universe_of; use_bv_sorts = uu___110_1353.use_bv_sorts; qname_and_index = uu___110_1353.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (

let uu____1375 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____1375)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____1378 -> (

let uu____1379 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1379)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____1402) -> begin
(

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (

let uu____1418 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____1418)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___93_1423 -> (match (uu___93_1423) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____1437 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____1447 = (inst_tscheme t)
in (match (uu____1447) with
| (us, t) -> begin
(

let uu____1454 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (uu____1454)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____1466 -> (match (uu____1466) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs))) with
| true -> begin
(

let uu____1480 = (

let uu____1481 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (

let uu____1484 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____1487 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1488 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____1481 uu____1484 uu____1487 uu____1488)))))
in (failwith uu____1480))
end
| uu____1489 -> begin
()
end);
(

let uu____1490 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd uu____1490));
))
end
| uu____1494 -> begin
(

let uu____1495 = (

let uu____1496 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____1496))
in (failwith uu____1495))
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
| uu____1500 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____1504 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____1508 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____1516 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match (((c), (l))) with
| ([], uu____1534) -> begin
Maybe
end
| (uu____1538, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| uu____1550 -> begin
No
end))
in (aux cur lns))))
end
| uu____1555 -> begin
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

let uu____1602 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____1602) with
| None -> begin
(FStar_Util.find_map env.gamma (fun uu___94_1619 -> (match (uu___94_1619) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____1638 = (

let uu____1646 = (inst_tscheme t)
in FStar_Util.Inl (uu____1646))
in Some (uu____1638))
end
| uu____1661 -> begin
None
end)
end
| Binding_sig (uu____1669, FStar_Syntax_Syntax.Sig_bundle (ses, uu____1671, uu____1672, uu____1673)) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____1683 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1683) with
| true -> begin
(cache (FStar_Util.Inr (((se), (None)))))
end
| uu____1692 -> begin
None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1703) -> begin
Some (t)
end
| uu____1710 -> begin
(cache t)
end))
in (

let uu____1711 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1711) with
| true -> begin
(maybe_cache (FStar_Util.Inr (((s), (None)))))
end
| uu____1727 -> begin
None
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____1740 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1740) with
| true -> begin
Some (FStar_Util.Inr (((s), (Some (us)))))
end
| uu____1763 -> begin
None
end))
end
| uu____1771 -> begin
None
end)))
end
| se -> begin
se
end))
end
| uu____1781 -> begin
None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____1804 -> begin
(

let uu____1805 = ((cur_mod <> Yes) || (has_interface env env.curmodule))
in (match (uu____1805) with
| true -> begin
(

let uu____1814 = (find_in_sigtab env lid)
in (match (uu____1814) with
| Some (se) -> begin
Some (FStar_Util.Inr (((se), (None))))
end
| None -> begin
None
end))
end
| uu____1845 -> begin
None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1865, uu____1866, uu____1867) -> begin
(add_sigelts env ses)
end
| uu____1874 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1880) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____1884 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___95_1900 -> (match (uu___95_1900) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| uu____1907 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____1922, (lb)::[]), uu____1924, uu____1925, uu____1926, uu____1927) -> begin
(

let uu____1938 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (uu____1938))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1946, lbs), uu____1948, uu____1949, uu____1950, uu____1951) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1969) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____1974 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1974) with
| true -> begin
(

let uu____1978 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (uu____1978))
end
| uu____1986 -> begin
None
end))
end)))
end
| uu____1989 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____2002) -> begin
(

let uu____2003 = (

let uu____2006 = (

let uu____2007 = (

let uu____2010 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____2010))
in ((ne.FStar_Syntax_Syntax.univs), (uu____2007)))
in (inst_tscheme uu____2006))
in Some (uu____2003))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____2020, uu____2021, uu____2022, uu____2023) -> begin
(

let uu____2028 = (

let uu____2031 = (

let uu____2032 = (

let uu____2035 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____2035))
in ((us), (uu____2032)))
in (inst_tscheme uu____2031))
in Some (uu____2028))
end
| uu____2042 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun uu___96_2069 -> (match (uu___96_2069) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2090, uvs, t, uu____2093, uu____2094, uu____2095, uu____2096, uu____2097), None) -> begin
(

let uu____2108 = (inst_tscheme ((uvs), (t)))
in Some (uu____2108))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, uu____2117), None) -> begin
(

let uu____2126 = (

let uu____2127 = (in_cur_mod env l)
in (uu____2127 = Yes))
in (match (uu____2126) with
| true -> begin
(

let uu____2131 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____2131) with
| true -> begin
(

let uu____2136 = (inst_tscheme ((uvs), (t)))
in Some (uu____2136))
end
| uu____2141 -> begin
None
end))
end
| uu____2144 -> begin
(

let uu____2145 = (inst_tscheme ((uvs), (t)))
in Some (uu____2145))
end))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2154, uu____2155, uu____2156, uu____2157), None) -> begin
(match (tps) with
| [] -> begin
(

let uu____2175 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _0_28 -> Some (_0_28)) uu____2175))
end
| uu____2185 -> begin
(

let uu____2186 = (

let uu____2189 = (

let uu____2190 = (

let uu____2193 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2193))
in ((uvs), (uu____2190)))
in (inst_tscheme uu____2189))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____2186))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2209, uu____2210, uu____2211, uu____2212), Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____2231 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____2231))
end
| uu____2241 -> begin
(

let uu____2242 = (

let uu____2245 = (

let uu____2246 = (

let uu____2249 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2249))
in ((uvs), (uu____2246)))
in (inst_tscheme_with uu____2245 us))
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____2242))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (uu____2273), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| uu____2284 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (

let uu____2289 = (

let uu____2293 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____2293 mapper))
in (match (uu____2289) with
| Some (us, t) -> begin
Some (((us), ((

let uu___111_2326 = t
in {FStar_Syntax_Syntax.n = uu___111_2326.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___111_2326.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___111_2326.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____2343 = (lookup_qname env l)
in (match (uu____2343) with
| None -> begin
false
end
| Some (uu____2359) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (

let uu____2380 = (try_lookup_bv env bv)
in (match (uu____2380) with
| None -> begin
(

let uu____2386 = (

let uu____2387 = (

let uu____2390 = (variable_not_found bv)
in (

let uu____2391 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____2390), (uu____2391))))
in FStar_Errors.Error (uu____2387))
in (Prims.raise uu____2386))
end
| Some (t) -> begin
(

let uu____2397 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range uu____2397 t))
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (

let uu____2407 = (try_lookup_lid_aux env l)
in (match (uu____2407) with
| None -> begin
None
end
| Some (us, t) -> begin
(

let uu____2432 = (

let uu____2435 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (uu____2435)))
in Some (uu____2432))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (

let uu____2446 = (try_lookup_lid env l)
in (match (uu____2446) with
| None -> begin
(

let uu____2454 = (

let uu____2455 = (

let uu____2458 = (name_not_found l)
in ((uu____2458), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____2455))
in (Prims.raise uu____2454))
end
| Some (us, t) -> begin
((us), (t))
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___97_2472 -> (match (uu___97_2472) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____2474 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (

let uu____2485 = (lookup_qname env lid)
in (match (uu____2485) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2498, uvs, t, q, uu____2502), None)) -> begin
(

let uu____2518 = (

let uu____2524 = (

let uu____2527 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____2527)))
in ((uu____2524), (q)))
in Some (uu____2518))
end
| uu____2536 -> begin
None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2556 = (lookup_qname env lid)
in (match (uu____2556) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2567, uvs, t, uu____2570, uu____2571), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2587 -> begin
(

let uu____2596 = (

let uu____2597 = (

let uu____2600 = (name_not_found lid)
in ((uu____2600), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2597))
in (Prims.raise uu____2596))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2611 = (lookup_qname env lid)
in (match (uu____2611) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2622, uvs, t, uu____2625, uu____2626, uu____2627, uu____2628, uu____2629), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2647 -> begin
(

let uu____2656 = (

let uu____2657 = (

let uu____2660 = (name_not_found lid)
in ((uu____2660), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2657))
in (Prims.raise uu____2656))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____2672 = (lookup_qname env lid)
in (match (uu____2672) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____2684, uu____2685, uu____2686, uu____2687, uu____2688, dcs, uu____2690, uu____2691), uu____2692)) -> begin
((true), (dcs))
end
| uu____2714 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____2730 = (lookup_qname env lid)
in (match (uu____2730) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2739, uu____2740, uu____2741, l, uu____2743, uu____2744, uu____2745, uu____2746), uu____2747)) -> begin
l
end
| uu____2766 -> begin
(

let uu____2775 = (

let uu____2776 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____2776))
in (failwith uu____2775))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____2800 = (lookup_qname env lid)
in (match (uu____2800) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____2829, lbs), uu____2831, uu____2832, quals, uu____2834) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2851 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____2851) with
| true -> begin
(

let uu____2856 = (

let uu____2860 = (

let uu____2861 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) uu____2861))
in ((lb.FStar_Syntax_Syntax.lbunivs), (uu____2860)))
in Some (uu____2856))
end
| uu____2866 -> begin
None
end)))))
end
| uu____2870 -> begin
None
end)
end
| uu____2873 -> begin
None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (

let uu____2892 = (lookup_qname env ftv)
in (match (uu____2892) with
| Some (FStar_Util.Inr (se, None)) -> begin
(

let uu____2916 = (effect_signature se)
in (match (uu____2916) with
| None -> begin
None
end
| Some (uu____2923, t) -> begin
(

let uu____2927 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (uu____2927))
end))
end
| uu____2928 -> begin
None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____2943 = (try_lookup_effect_lid env ftv)
in (match (uu____2943) with
| None -> begin
(

let uu____2945 = (

let uu____2946 = (

let uu____2949 = (name_not_found ftv)
in ((uu____2949), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____2946))
in (Prims.raise uu____2945))
end
| Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (

let uu____2963 = (lookup_qname env lid0)
in (match (uu____2963) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, uu____2980, uu____2981), None)) -> begin
(

let lid = (

let uu____3000 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____3000))
in (

let uu____3001 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___98_3003 -> (match (uu___98_3003) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____3004 -> begin
false
end))))
in (match (uu____3001) with
| true -> begin
None
end
| uu____3010 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs))) with
| true -> begin
univ_insts
end
| uu____3016 -> begin
(match (((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) && ((FStar_List.length univ_insts) = (Prims.parse_int "1")))) with
| true -> begin
(FStar_List.append univ_insts ((FStar_Syntax_Syntax.U_zero)::[]))
end
| uu____3019 -> begin
(

let uu____3020 = (

let uu____3021 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____3022 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" uu____3021 uu____3022)))
in (failwith uu____3020))
end)
end)
in (match (((binders), (univs))) with
| ([], uu____3028) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____3037, (uu____3038)::(uu____3039)::uu____3040) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(

let uu____3043 = (

let uu____3044 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____3045 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____3044 uu____3045)))
in (failwith uu____3043))
end
| uu____3051 -> begin
(

let uu____3054 = (

let uu____3057 = (

let uu____3058 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (uu____3058)))
in (inst_tscheme_with uu____3057 insts))
in (match (uu____3054) with
| (uu____3066, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (

let uu____3069 = (

let uu____3070 = (FStar_Syntax_Subst.compress t)
in uu____3070.FStar_Syntax_Syntax.n)
in (match (uu____3069) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| uu____3100 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____3104 -> begin
None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (

let uu____3128 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)
in (match (uu____3128) with
| None -> begin
None
end
| Some (uu____3135, c) -> begin
(

let l = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____3140 = (find l)
in (match (uu____3140) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end)))
end)))
in (

let res = (

let uu____3145 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____3145) with
| Some (l) -> begin
l
end
| None -> begin
(

let uu____3148 = (find l)
in (match (uu____3148) with
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

let uu____3160 = (lookup_qname env l)
in (match (uu____3160) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3171), uu____3172)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| uu____3187 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____3208 -> (

let uu____3209 = (

let uu____3210 = (FStar_Util.string_of_int i)
in (

let uu____3211 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____3210 uu____3211)))
in (failwith uu____3209)))
in (

let uu____3212 = (lookup_datacon env lid)
in (match (uu____3212) with
| (uu____3215, t) -> begin
(

let uu____3217 = (

let uu____3218 = (FStar_Syntax_Subst.compress t)
in uu____3218.FStar_Syntax_Syntax.n)
in (match (uu____3217) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____3222) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____3237 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____3243 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right uu____3243 Prims.fst)))
end)
end
| uu____3248 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____3255 = (lookup_qname env l)
in (match (uu____3255) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____3264, uu____3265, uu____3266, quals, uu____3268), uu____3269)) -> begin
(FStar_Util.for_some (fun uu___99_3286 -> (match (uu___99_3286) with
| FStar_Syntax_Syntax.Projector (uu____3287) -> begin
true
end
| uu____3290 -> begin
false
end)) quals)
end
| uu____3291 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3306 = (lookup_qname env lid)
in (match (uu____3306) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____3315, uu____3316, uu____3317, uu____3318, uu____3319, uu____3320, uu____3321, uu____3322), uu____3323)) -> begin
true
end
| uu____3342 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3357 = (lookup_qname env lid)
in (match (uu____3357) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3366, uu____3367, uu____3368, uu____3369, uu____3370, uu____3371, tags, uu____3373), uu____3374)) -> begin
(FStar_Util.for_some (fun uu___100_3395 -> (match (uu___100_3395) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3398 -> begin
false
end)) tags)
end
| uu____3399 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3414 = (lookup_qname env lid)
in (match (uu____3414) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_let (uu____3423, uu____3424, uu____3425, tags, uu____3427), uu____3428)) -> begin
(FStar_Util.for_some (fun uu___101_3449 -> (match (uu___101_3449) with
| FStar_Syntax_Syntax.Action (uu____3450) -> begin
true
end
| uu____3451 -> begin
false
end)) tags)
end
| uu____3452 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (

let uu____3469 = (

let uu____3470 = (FStar_Syntax_Util.un_uinst head)
in uu____3470.FStar_Syntax_Syntax.n)
in (match (uu____3469) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____3474 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun uu___102_3492 -> (match (uu___102_3492) with
| FStar_Util.Inl (uu____3501) -> begin
Some (false)
end
| FStar_Util.Inr (se, uu____3510) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____3519, uu____3520, uu____3521, qs, uu____3523) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3526) -> begin
Some (true)
end
| uu____3538 -> begin
Some (false)
end)
end))
in (

let uu____3539 = (

let uu____3541 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____3541 mapper))
in (match (uu____3539) with
| Some (b) -> begin
b
end
| None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____3564 = (lookup_qname env lid)
in (match (uu____3564) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3573, uu____3574, tps, uu____3576, uu____3577, uu____3578, uu____3579, uu____3580), uu____3581)) -> begin
(FStar_List.length tps)
end
| uu____3605 -> begin
(

let uu____3614 = (

let uu____3615 = (

let uu____3618 = (name_not_found lid)
in ((uu____3618), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____3615))
in (Prims.raise uu____3614))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____3635 = (effect_decl_opt env l)
in (match (uu____3635) with
| None -> begin
(

let uu____3637 = (

let uu____3638 = (

let uu____3641 = (name_not_found l)
in ((uu____3641), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3638))
in (Prims.raise uu____3637))
end
| Some (md) -> begin
md
end)))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3689 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3713 -> begin
(

let uu____3714 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____3738 -> (match (uu____3738) with
| (m1, m2, uu____3746, uu____3747, uu____3748) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____3714) with
| None -> begin
(

let uu____3765 = (

let uu____3766 = (

let uu____3769 = (

let uu____3770 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____3771 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____3770 uu____3771)))
in ((uu____3769), (env.range)))
in FStar_Errors.Error (uu____3766))
in (Prims.raise uu____3765))
end
| Some (uu____3783, uu____3784, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)))) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end
| uu____3815 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____3831 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))
in (match (uu____3831) with
| None -> begin
(

let uu____3840 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____3840))
end
| Some (md) -> begin
(

let uu____3846 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____3846) with
| (uu____3853, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____3861))::((wp, uu____3863))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____3885 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (Some (res_u)))
end
| uu____3912 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (Some (res_u)))
end
| uu____3913 -> begin
(

let eff_name = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____3920 = (get_range env)
in (

let uu____3921 = (

let uu____3924 = (

let uu____3925 = (

let uu____3935 = (

let uu____3937 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____3937)::[])
in ((null_wp), (uu____3935)))
in FStar_Syntax_Syntax.Tm_app (uu____3925))
in (FStar_Syntax_Syntax.mk uu____3924))
in (uu____3921 None uu____3920)))
in (

let uu____3947 = (

let uu____3948 = (

let uu____3954 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____3954)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____3948; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____3947))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3962) -> begin
(

let effects = (

let uu___112_3964 = env.effects
in {decls = (ne)::env.effects.decls; order = uu___112_3964.order; joins = uu___112_3964.joins})
in (

let uu___113_3965 = env
in {solver = uu___113_3965.solver; range = uu___113_3965.range; curmodule = uu___113_3965.curmodule; gamma = uu___113_3965.gamma; gamma_cache = uu___113_3965.gamma_cache; modules = uu___113_3965.modules; expected_typ = uu___113_3965.expected_typ; sigtab = uu___113_3965.sigtab; is_pattern = uu___113_3965.is_pattern; instantiate_imp = uu___113_3965.instantiate_imp; effects = effects; generalize = uu___113_3965.generalize; letrecs = uu___113_3965.letrecs; top_level = uu___113_3965.top_level; check_uvars = uu___113_3965.check_uvars; use_eq = uu___113_3965.use_eq; is_iface = uu___113_3965.is_iface; admit = uu___113_3965.admit; lax = uu___113_3965.lax; lax_universes = uu___113_3965.lax_universes; type_of = uu___113_3965.type_of; universe_of = uu___113_3965.universe_of; use_bv_sorts = uu___113_3965.use_bv_sorts; qname_and_index = uu___113_3965.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, uu____3967) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (

let uu____3977 = (e1.mlift r wp1)
in (e2.mlift r uu____3977)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let uu____3990 = (inst_tscheme lift_t)
in (match (uu____3990) with
| (uu____3995, lift_t) -> begin
(

let uu____3997 = (

let uu____4000 = (

let uu____4001 = (

let uu____4011 = (

let uu____4013 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____4014 = (

let uu____4016 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____4016)::[])
in (uu____4013)::uu____4014))
in ((lift_t), (uu____4011)))
in FStar_Syntax_Syntax.Tm_app (uu____4001))
in (FStar_Syntax_Syntax.mk uu____4000))
in (uu____3997 None wp1.FStar_Syntax_Syntax.pos))
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

let uu____4050 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____4050 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (

let uu____4052 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____4052 FStar_Syntax_Syntax.Delta_constant None))
in (

let uu____4053 = (l arg wp)
in (FStar_Syntax_Print.term_to_string uu____4053)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order uu____4071 -> (match (uu____4071) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_32 -> Some (_0_32)))
end
| uu____4080 -> begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (

let uu____4092 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____4098 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____4103 -> begin
(

let uu____4104 = (

let uu____4109 = (find_edge order ((i), (k)))
in (

let uu____4111 = (find_edge order ((k), (j)))
in ((uu____4109), (uu____4111))))
in (match (uu____4104) with
| (Some (e1), Some (e2)) -> begin
(

let uu____4120 = (compose_edges e1 e2)
in (uu____4120)::[])
end
| uu____4121 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order uu____4092))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in ((FStar_All.pipe_right order (FStar_List.iter (fun edge -> (

let uu____4133 = ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (

let uu____4134 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right uu____4134 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____4133) with
| true -> begin
(

let uu____4137 = (

let uu____4138 = (

let uu____4141 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (

let uu____4142 = (get_range env)
in ((uu____4141), (uu____4142))))
in FStar_Errors.Error (uu____4138))
in (Prims.raise uu____4137))
end
| uu____4143 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____4237 = (

let uu____4242 = (find_edge order ((i), (k)))
in (

let uu____4244 = (find_edge order ((j), (k)))
in ((uu____4242), (uu____4244))))
in (match (uu____4237) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, uu____4267, uu____4268) -> begin
(

let uu____4272 = ((

let uu____4273 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some uu____4273)) && (

let uu____4275 = (

let uu____4276 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some uu____4276))
in (not (uu____4275))))
in (match (uu____4272) with
| true -> begin
Some (((k), (ik), (jk)))
end
| uu____4285 -> begin
bopt
end))
end)
end
| uu____4286 -> begin
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

let uu___114_4365 = env.effects
in {decls = uu___114_4365.decls; order = order; joins = joins})
in (

let uu___115_4366 = env
in {solver = uu___115_4366.solver; range = uu___115_4366.range; curmodule = uu___115_4366.curmodule; gamma = uu___115_4366.gamma; gamma_cache = uu___115_4366.gamma_cache; modules = uu___115_4366.modules; expected_typ = uu___115_4366.expected_typ; sigtab = uu___115_4366.sigtab; is_pattern = uu___115_4366.is_pattern; instantiate_imp = uu___115_4366.instantiate_imp; effects = effects; generalize = uu___115_4366.generalize; letrecs = uu___115_4366.letrecs; top_level = uu___115_4366.top_level; check_uvars = uu___115_4366.check_uvars; use_eq = uu___115_4366.use_eq; is_iface = uu___115_4366.is_iface; admit = uu___115_4366.admit; lax = uu___115_4366.lax; lax_universes = uu___115_4366.lax_universes; type_of = uu___115_4366.type_of; universe_of = uu___115_4366.universe_of; use_bv_sorts = uu___115_4366.use_bv_sorts; qname_and_index = uu___115_4366.qname_and_index})));
))))))))))))
end
| uu____4367 -> begin
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

let uu____4392 = (push x rest)
in (local)::uu____4392)
end))
in (

let uu___116_4394 = env
in (

let uu____4395 = (push s env.gamma)
in {solver = uu___116_4394.solver; range = uu___116_4394.range; curmodule = uu___116_4394.curmodule; gamma = uu____4395; gamma_cache = uu___116_4394.gamma_cache; modules = uu___116_4394.modules; expected_typ = uu___116_4394.expected_typ; sigtab = uu___116_4394.sigtab; is_pattern = uu___116_4394.is_pattern; instantiate_imp = uu___116_4394.instantiate_imp; effects = uu___116_4394.effects; generalize = uu___116_4394.generalize; letrecs = uu___116_4394.letrecs; top_level = uu___116_4394.top_level; check_uvars = uu___116_4394.check_uvars; use_eq = uu___116_4394.use_eq; is_iface = uu___116_4394.is_iface; admit = uu___116_4394.admit; lax = uu___116_4394.lax; lax_universes = uu___116_4394.lax_universes; type_of = uu___116_4394.type_of; universe_of = uu___116_4394.universe_of; use_bv_sorts = uu___116_4394.use_bv_sorts; qname_and_index = uu___116_4394.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___117_4422 = env
in {solver = uu___117_4422.solver; range = uu___117_4422.range; curmodule = uu___117_4422.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___117_4422.gamma_cache; modules = uu___117_4422.modules; expected_typ = uu___117_4422.expected_typ; sigtab = uu___117_4422.sigtab; is_pattern = uu___117_4422.is_pattern; instantiate_imp = uu___117_4422.instantiate_imp; effects = uu___117_4422.effects; generalize = uu___117_4422.generalize; letrecs = uu___117_4422.letrecs; top_level = uu___117_4422.top_level; check_uvars = uu___117_4422.check_uvars; use_eq = uu___117_4422.use_eq; is_iface = uu___117_4422.is_iface; admit = uu___117_4422.admit; lax = uu___117_4422.lax; lax_universes = uu___117_4422.lax_universes; type_of = uu___117_4422.type_of; universe_of = uu___117_4422.universe_of; use_bv_sorts = uu___117_4422.use_bv_sorts; qname_and_index = uu___117_4422.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env uu____4438 -> (match (uu____4438) with
| (x, uu____4442) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let x = (

let uu___118_4462 = x
in {FStar_Syntax_Syntax.ppname = uu___118_4462.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_4462.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___119_4492 = env
in {solver = uu___119_4492.solver; range = uu___119_4492.range; curmodule = uu___119_4492.curmodule; gamma = []; gamma_cache = uu___119_4492.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = uu___119_4492.sigtab; is_pattern = uu___119_4492.is_pattern; instantiate_imp = uu___119_4492.instantiate_imp; effects = uu___119_4492.effects; generalize = uu___119_4492.generalize; letrecs = uu___119_4492.letrecs; top_level = uu___119_4492.top_level; check_uvars = uu___119_4492.check_uvars; use_eq = uu___119_4492.use_eq; is_iface = uu___119_4492.is_iface; admit = uu___119_4492.admit; lax = uu___119_4492.lax; lax_universes = uu___119_4492.lax_universes; type_of = uu___119_4492.type_of; universe_of = uu___119_4492.universe_of; use_bv_sorts = uu___119_4492.use_bv_sorts; qname_and_index = uu___119_4492.qname_and_index});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___120_4507 = env
in {solver = uu___120_4507.solver; range = uu___120_4507.range; curmodule = uu___120_4507.curmodule; gamma = uu___120_4507.gamma; gamma_cache = uu___120_4507.gamma_cache; modules = uu___120_4507.modules; expected_typ = Some (t); sigtab = uu___120_4507.sigtab; is_pattern = uu___120_4507.is_pattern; instantiate_imp = uu___120_4507.instantiate_imp; effects = uu___120_4507.effects; generalize = uu___120_4507.generalize; letrecs = uu___120_4507.letrecs; top_level = uu___120_4507.top_level; check_uvars = uu___120_4507.check_uvars; use_eq = false; is_iface = uu___120_4507.is_iface; admit = uu___120_4507.admit; lax = uu___120_4507.lax; lax_universes = uu___120_4507.lax_universes; type_of = uu___120_4507.type_of; universe_of = uu___120_4507.universe_of; use_bv_sorts = uu___120_4507.use_bv_sorts; qname_and_index = uu___120_4507.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (

let uu____4520 = (expected_typ env)
in (((

let uu___121_4523 = env
in {solver = uu___121_4523.solver; range = uu___121_4523.range; curmodule = uu___121_4523.curmodule; gamma = uu___121_4523.gamma; gamma_cache = uu___121_4523.gamma_cache; modules = uu___121_4523.modules; expected_typ = None; sigtab = uu___121_4523.sigtab; is_pattern = uu___121_4523.is_pattern; instantiate_imp = uu___121_4523.instantiate_imp; effects = uu___121_4523.effects; generalize = uu___121_4523.generalize; letrecs = uu___121_4523.letrecs; top_level = uu___121_4523.top_level; check_uvars = uu___121_4523.check_uvars; use_eq = false; is_iface = uu___121_4523.is_iface; admit = uu___121_4523.admit; lax = uu___121_4523.lax; lax_universes = uu___121_4523.lax_universes; type_of = uu___121_4523.type_of; universe_of = uu___121_4523.universe_of; use_bv_sorts = uu___121_4523.use_bv_sorts; qname_and_index = uu___121_4523.qname_and_index})), (uu____4520))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
(

let uu____4534 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___103_4538 -> (match (uu___103_4538) with
| Binding_sig (uu____4540, se) -> begin
(se)::[]
end
| uu____4544 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4534 FStar_List.rev))
end
| uu____4547 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___122_4549 = env
in {solver = uu___122_4549.solver; range = uu___122_4549.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___122_4549.gamma_cache; modules = (m)::env.modules; expected_typ = uu___122_4549.expected_typ; sigtab = uu___122_4549.sigtab; is_pattern = uu___122_4549.is_pattern; instantiate_imp = uu___122_4549.instantiate_imp; effects = uu___122_4549.effects; generalize = uu___122_4549.generalize; letrecs = uu___122_4549.letrecs; top_level = uu___122_4549.top_level; check_uvars = uu___122_4549.check_uvars; use_eq = uu___122_4549.use_eq; is_iface = uu___122_4549.is_iface; admit = uu___122_4549.admit; lax = uu___122_4549.lax; lax_universes = uu___122_4549.lax_universes; type_of = uu___122_4549.type_of; universe_of = uu___122_4549.universe_of; use_bv_sorts = uu___122_4549.use_bv_sorts; qname_and_index = uu___122_4549.qname_and_index});
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
| (Binding_univ (uu____4599))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4614 = (

let uu____4618 = (FStar_Syntax_Free.uvars t)
in (ext out uu____4618))
in (aux uu____4614 tl))
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

let uu____4674 = (

let uu____4676 = (FStar_Syntax_Free.univs t)
in (ext out uu____4676))
in (aux uu____4674 tl))
end
| (Binding_sig (uu____4678))::uu____4679 -> begin
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
| (Binding_sig_inst (uu____4716))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(

let uu____4726 = (FStar_Util.set_add uname out)
in (aux uu____4726 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4740 = (

let uu____4742 = (FStar_Syntax_Free.univnames t)
in (ext out uu____4742))
in (aux uu____4740 tl))
end
| (Binding_sig (uu____4744))::uu____4745 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___104_4761 -> (match (uu___104_4761) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____4773 = (

let uu____4775 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____4775 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____4773 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___105_4826 -> (match (uu___105_4826) with
| Binding_sig (lids, uu____4830) -> begin
(FStar_List.append lids keys)
end
| uu____4833 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____4835 v keys -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)) keys)))


let dummy_solver : solver_t = {init = (fun uu____4839 -> ()); push = (fun uu____4840 -> ()); pop = (fun uu____4841 -> ()); mark = (fun uu____4842 -> ()); reset_mark = (fun uu____4843 -> ()); commit_mark = (fun uu____4844 -> ()); encode_modul = (fun uu____4845 uu____4846 -> ()); encode_sig = (fun uu____4847 uu____4848 -> ()); solve = (fun uu____4849 uu____4850 uu____4851 -> ()); is_trivial = (fun uu____4855 uu____4856 -> false); finish = (fun uu____4857 -> ()); refresh = (fun uu____4858 -> ())}




