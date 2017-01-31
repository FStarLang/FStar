
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


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _0_171 = (new_gamma_cache ())
in (let _0_170 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _0_171; modules = []; expected_typ = None; sigtab = _0_170; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)

type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun uu____953 -> (

let uu____954 = (FStar_ST.read query_indices)
in (match (uu____954) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____968 -> begin
(let _0_174 = (let _0_173 = (FStar_List.hd (FStar_ST.read query_indices))
in (let _0_172 = (FStar_ST.read query_indices)
in (_0_173)::_0_172))
in (FStar_ST.write query_indices _0_174))
end)))
in (

let pop_query_indices = (fun uu____1000 -> (

let uu____1001 = (FStar_ST.read query_indices)
in (match (uu____1001) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd)::tl -> begin
(FStar_ST.write query_indices tl)
end)))
in (

let add_query_index = (fun uu____1038 -> (match (uu____1038) with
| (l, n) -> begin
(

let uu____1043 = (FStar_ST.read query_indices)
in (match (uu____1043) with
| (hd)::tl -> begin
(FStar_ST.write query_indices (((((l), (n)))::hd)::tl))
end
| uu____1077 -> begin
(failwith "Empty query indices")
end))
end))
in (

let peek_query_indices = (fun uu____1088 -> (FStar_List.hd (FStar_ST.read query_indices)))
in (

let commit_query_index_mark = (fun uu____1101 -> (

let uu____1102 = (FStar_ST.read query_indices)
in (match (uu____1102) with
| (hd)::(uu____1114)::tl -> begin
(FStar_ST.write query_indices ((hd)::tl))
end
| uu____1141 -> begin
(failwith "Unmarked query index stack")
end)))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> ((let _0_176 = (let _0_175 = (FStar_ST.read stack)
in (env)::_0_175)
in (FStar_ST.write stack _0_176));
(

let uu___106_1162 = env
in (let _0_178 = (FStar_Util.smap_copy (gamma_cache env))
in (let _0_177 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___106_1162.solver; range = uu___106_1162.range; curmodule = uu___106_1162.curmodule; gamma = uu___106_1162.gamma; gamma_cache = _0_178; modules = uu___106_1162.modules; expected_typ = uu___106_1162.expected_typ; sigtab = _0_177; is_pattern = uu___106_1162.is_pattern; instantiate_imp = uu___106_1162.instantiate_imp; effects = uu___106_1162.effects; generalize = uu___106_1162.generalize; letrecs = uu___106_1162.letrecs; top_level = uu___106_1162.top_level; check_uvars = uu___106_1162.check_uvars; use_eq = uu___106_1162.use_eq; is_iface = uu___106_1162.is_iface; admit = uu___106_1162.admit; lax = uu___106_1162.lax; lax_universes = uu___106_1162.lax_universes; type_of = uu___106_1162.type_of; universe_of = uu___106_1162.universe_of; use_bv_sorts = uu___106_1162.use_bv_sorts; qname_and_index = uu___106_1162.qname_and_index})));
))
in (

let pop_stack = (fun env -> (

let uu____1167 = (FStar_ST.read stack)
in (match (uu____1167) with
| (env)::tl -> begin
((FStar_ST.write stack tl);
env;
)
end
| uu____1179 -> begin
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
(Prims.ignore (pop_stack env));
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

let uu____1221 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____1233 -> (match (uu____1233) with
| (m, uu____1237) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____1221) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___107_1242 = env
in {solver = uu___107_1242.solver; range = uu___107_1242.range; curmodule = uu___107_1242.curmodule; gamma = uu___107_1242.gamma; gamma_cache = uu___107_1242.gamma_cache; modules = uu___107_1242.modules; expected_typ = uu___107_1242.expected_typ; sigtab = uu___107_1242.sigtab; is_pattern = uu___107_1242.is_pattern; instantiate_imp = uu___107_1242.instantiate_imp; effects = uu___107_1242.effects; generalize = uu___107_1242.generalize; letrecs = uu___107_1242.letrecs; top_level = uu___107_1242.top_level; check_uvars = uu___107_1242.check_uvars; use_eq = uu___107_1242.use_eq; is_iface = uu___107_1242.is_iface; admit = uu___107_1242.admit; lax = uu___107_1242.lax; lax_universes = uu___107_1242.lax_universes; type_of = uu___107_1242.type_of; universe_of = uu___107_1242.universe_of; use_bv_sorts = uu___107_1242.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end
| Some (uu____1245, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___108_1251 = env
in {solver = uu___108_1251.solver; range = uu___108_1251.range; curmodule = uu___108_1251.curmodule; gamma = uu___108_1251.gamma; gamma_cache = uu___108_1251.gamma_cache; modules = uu___108_1251.modules; expected_typ = uu___108_1251.expected_typ; sigtab = uu___108_1251.sigtab; is_pattern = uu___108_1251.is_pattern; instantiate_imp = uu___108_1251.instantiate_imp; effects = uu___108_1251.effects; generalize = uu___108_1251.generalize; letrecs = uu___108_1251.letrecs; top_level = uu___108_1251.top_level; check_uvars = uu___108_1251.check_uvars; use_eq = uu___108_1251.use_eq; is_iface = uu___108_1251.is_iface; admit = uu___108_1251.admit; lax = uu___108_1251.lax; lax_universes = uu___108_1251.lax_universes; type_of = uu___108_1251.type_of; universe_of = uu___108_1251.universe_of; use_bv_sorts = uu___108_1251.use_bv_sorts; qname_and_index = Some (((l), (next)))});
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
| uu____1298 -> begin
(

let uu___109_1299 = e
in {solver = uu___109_1299.solver; range = r; curmodule = uu___109_1299.curmodule; gamma = uu___109_1299.gamma; gamma_cache = uu___109_1299.gamma_cache; modules = uu___109_1299.modules; expected_typ = uu___109_1299.expected_typ; sigtab = uu___109_1299.sigtab; is_pattern = uu___109_1299.is_pattern; instantiate_imp = uu___109_1299.instantiate_imp; effects = uu___109_1299.effects; generalize = uu___109_1299.generalize; letrecs = uu___109_1299.letrecs; top_level = uu___109_1299.top_level; check_uvars = uu___109_1299.check_uvars; use_eq = uu___109_1299.use_eq; is_iface = uu___109_1299.is_iface; admit = uu___109_1299.admit; lax = uu___109_1299.lax; lax_universes = uu___109_1299.lax_universes; type_of = uu___109_1299.type_of; universe_of = uu___109_1299.universe_of; use_bv_sorts = uu___109_1299.use_bv_sorts; qname_and_index = uu___109_1299.qname_and_index})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___110_1316 = env
in {solver = uu___110_1316.solver; range = uu___110_1316.range; curmodule = lid; gamma = uu___110_1316.gamma; gamma_cache = uu___110_1316.gamma_cache; modules = uu___110_1316.modules; expected_typ = uu___110_1316.expected_typ; sigtab = uu___110_1316.sigtab; is_pattern = uu___110_1316.is_pattern; instantiate_imp = uu___110_1316.instantiate_imp; effects = uu___110_1316.effects; generalize = uu___110_1316.generalize; letrecs = uu___110_1316.letrecs; top_level = uu___110_1316.top_level; check_uvars = uu___110_1316.check_uvars; use_eq = uu___110_1316.use_eq; is_iface = uu___110_1316.is_iface; admit = uu___110_1316.admit; lax = uu___110_1316.lax; lax_universes = uu___110_1316.lax_universes; type_of = uu___110_1316.type_of; universe_of = uu___110_1316.universe_of; use_bv_sorts = uu___110_1316.use_bv_sorts; qname_and_index = uu___110_1316.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _0_179 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _0_179)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____1340 -> FStar_Syntax_Syntax.U_unif ((FStar_Unionfind.fresh None)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____1361) -> begin
(

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _0_180 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_0_180)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___93_1381 -> (match (uu___93_1381) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____1395 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____1405 = (inst_tscheme t)
in (match (uu____1405) with
| (us, t) -> begin
(let _0_181 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (_0_181)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____1423 -> (match (uu____1423) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs))) with
| true -> begin
(failwith (let _0_185 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _0_184 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _0_183 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _0_182 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _0_185 _0_184 _0_183 _0_182))))))
end
| uu____1441 -> begin
()
end);
(Prims.snd (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts));
))
end
| uu____1443 -> begin
(failwith (let _0_186 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _0_186)))
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
| uu____1447 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____1451 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____1455 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____1463 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match (((c), (l))) with
| ([], uu____1481) -> begin
Maybe
end
| (uu____1485, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| uu____1497 -> begin
No
end))
in (aux cur lns))))
end
| uu____1502 -> begin
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

let uu____1549 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____1549) with
| None -> begin
(FStar_Util.find_map env.gamma (fun uu___94_1566 -> (match (uu___94_1566) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
Some (FStar_Util.Inl ((inst_tscheme t)))
end
| uu____1597 -> begin
None
end)
end
| Binding_sig (uu____1605, FStar_Syntax_Syntax.Sig_bundle (ses, uu____1607, uu____1608, uu____1609)) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____1619 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1619) with
| true -> begin
(cache (FStar_Util.Inr (((se), (None)))))
end
| uu____1628 -> begin
None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1639) -> begin
Some (t)
end
| uu____1646 -> begin
(cache t)
end))
in (

let uu____1647 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1647) with
| true -> begin
(maybe_cache (FStar_Util.Inr (((s), (None)))))
end
| uu____1663 -> begin
None
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____1676 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1676) with
| true -> begin
Some (FStar_Util.Inr (((s), (Some (us)))))
end
| uu____1699 -> begin
None
end))
end
| uu____1707 -> begin
None
end)))
end
| se -> begin
se
end))
end
| uu____1717 -> begin
None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____1740 -> begin
(

let uu____1741 = ((cur_mod <> Yes) || (has_interface env env.curmodule))
in (match (uu____1741) with
| true -> begin
(

let uu____1750 = (find_in_sigtab env lid)
in (match (uu____1750) with
| Some (se) -> begin
Some (FStar_Util.Inr (((se), (None))))
end
| None -> begin
None
end))
end
| uu____1781 -> begin
None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1801, uu____1802, uu____1803) -> begin
(add_sigelts env ses)
end
| uu____1810 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1816) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____1820 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___95_1836 -> (match (uu___95_1836) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| uu____1843 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____1858, (lb)::[]), uu____1860, uu____1861, uu____1862, uu____1863) -> begin
Some ((inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1879, lbs), uu____1881, uu____1882, uu____1883, uu____1884) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1902) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____1907 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1907) with
| true -> begin
Some ((inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))))
end
| uu____1916 -> begin
None
end))
end)))
end
| uu____1919 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1932) -> begin
Some ((inst_tscheme (let _0_188 = (let _0_187 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _0_187))
in ((ne.FStar_Syntax_Syntax.univs), (_0_188)))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____1940, uu____1941, uu____1942, uu____1943) -> begin
Some ((inst_tscheme (let _0_190 = (let _0_189 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _0_189))
in ((us), (_0_190)))))
end
| uu____1952 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun uu___96_1979 -> (match (uu___96_1979) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2000, uvs, t, uu____2003, uu____2004, uu____2005, uu____2006, uu____2007), None) -> begin
Some ((inst_tscheme ((uvs), (t))))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, uu____2024), None) -> begin
(

let uu____2033 = (let _0_191 = (in_cur_mod env l)
in (_0_191 = Yes))
in (match (uu____2033) with
| true -> begin
(

let uu____2037 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____2037) with
| true -> begin
Some ((inst_tscheme ((uvs), (t))))
end
| uu____2044 -> begin
None
end))
end
| uu____2047 -> begin
Some ((inst_tscheme ((uvs), (t))))
end))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2054, uu____2055, uu____2056, uu____2057), None) -> begin
(match (tps) with
| [] -> begin
(let _0_193 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _0_192 -> Some (_0_192)) _0_193))
end
| uu____2082 -> begin
(let _0_197 = (inst_tscheme (let _0_196 = (let _0_195 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _0_195))
in ((uvs), (_0_196))))
in (FStar_All.pipe_left (fun _0_194 -> Some (_0_194)) _0_197))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2096, uu____2097, uu____2098, uu____2099), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _0_199 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _0_198 -> Some (_0_198)) _0_199))
end
| uu____2125 -> begin
(let _0_204 = (let _0_203 = (let _0_202 = (let _0_201 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _0_201))
in ((uvs), (_0_202)))
in (inst_tscheme_with _0_203 us))
in (FStar_All.pipe_left (fun _0_200 -> Some (_0_200)) _0_204))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (uu____2147), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| uu____2158 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (

let uu____2163 = (let _0_205 = (lookup_qname env lid)
in (FStar_Util.bind_opt _0_205 mapper))
in (match (uu____2163) with
| Some (us, t) -> begin
Some (((us), ((

let uu___111_2191 = t
in {FStar_Syntax_Syntax.n = uu___111_2191.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___111_2191.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___111_2191.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____2208 = (lookup_qname env l)
in (match (uu____2208) with
| None -> begin
false
end
| Some (uu____2224) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (

let uu____2245 = (try_lookup_bv env bv)
in (match (uu____2245) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_207 = (variable_not_found bv)
in (let _0_206 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_0_207), (_0_206)))))))
end
| Some (t) -> begin
(let _0_208 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range _0_208 t))
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (

let uu____2265 = (try_lookup_lid_aux env l)
in (match (uu____2265) with
| None -> begin
None
end
| Some (us, t) -> begin
Some ((let _0_209 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (_0_209))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (

let uu____2300 = (try_lookup_lid env l)
in (match (uu____2300) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_210 = (name_not_found l)
in ((_0_210), ((FStar_Ident.range_of_lid l)))))))
end
| Some (us, t) -> begin
((us), (t))
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___97_2321 -> (match (uu___97_2321) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____2323 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (

let uu____2334 = (lookup_qname env lid)
in (match (uu____2334) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2347, uvs, t, q, uu____2351), None)) -> begin
Some ((let _0_212 = (let _0_211 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (_0_211)))
in ((_0_212), (q))))
end
| uu____2375 -> begin
None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2395 = (lookup_qname env lid)
in (match (uu____2395) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2406, uvs, t, uu____2409, uu____2410), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2426 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_213 = (name_not_found lid)
in ((_0_213), ((FStar_Ident.range_of_lid lid)))))))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2445 = (lookup_qname env lid)
in (match (uu____2445) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2456, uvs, t, uu____2459, uu____2460, uu____2461, uu____2462, uu____2463), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2481 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_214 = (name_not_found lid)
in ((_0_214), ((FStar_Ident.range_of_lid lid)))))))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (

let uu____2499 = (lookup_qname env lid)
in (match (uu____2499) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____2509, uu____2510, uu____2511, uu____2512, uu____2513, dcs, uu____2515, uu____2516), uu____2517)) -> begin
dcs
end
| uu____2538 -> begin
[]
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____2553 = (lookup_qname env lid)
in (match (uu____2553) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2562, uu____2563, uu____2564, l, uu____2566, uu____2567, uu____2568, uu____2569), uu____2570)) -> begin
l
end
| uu____2589 -> begin
(failwith (let _0_215 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _0_215)))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____2621 = (lookup_qname env lid)
in (match (uu____2621) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____2650, lbs), uu____2652, uu____2653, quals, uu____2655) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2672 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____2672) with
| true -> begin
Some ((let _0_217 = (let _0_216 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) _0_216))
in ((lb.FStar_Syntax_Syntax.lbunivs), (_0_217))))
end
| uu____2681 -> begin
None
end)))))
end
| uu____2685 -> begin
None
end)
end
| uu____2688 -> begin
None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (

let uu____2707 = (lookup_qname env ftv)
in (match (uu____2707) with
| Some (FStar_Util.Inr (se, None)) -> begin
(

let uu____2731 = (effect_signature se)
in (match (uu____2731) with
| None -> begin
None
end
| Some (uu____2738, t) -> begin
Some ((FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t))
end))
end
| uu____2742 -> begin
None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____2757 = (try_lookup_effect_lid env ftv)
in (match (uu____2757) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_218 = (name_not_found ftv)
in ((_0_218), ((FStar_Ident.range_of_lid ftv)))))))
end
| Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (

let uu____2772 = (lookup_qname env lid0)
in (match (uu____2772) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, uu____2789, uu____2790), None)) -> begin
(

let lid = (let _0_219 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid _0_219))
in (

let uu____2809 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___98_2811 -> (match (uu___98_2811) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____2812 -> begin
false
end))))
in (match (uu____2809) with
| true -> begin
None
end
| uu____2818 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs))) with
| true -> begin
univ_insts
end
| uu____2824 -> begin
(match (((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) && ((FStar_List.length univ_insts) = (Prims.parse_int "1")))) with
| true -> begin
(FStar_List.append univ_insts ((FStar_Syntax_Syntax.U_zero)::[]))
end
| uu____2827 -> begin
(failwith (let _0_221 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_220 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" _0_221 _0_220))))
end)
end)
in (match (((binders), (univs))) with
| ([], uu____2833) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____2842, (uu____2843)::(uu____2844)::uu____2845) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(failwith (let _0_223 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_222 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _0_223 _0_222))))
end
| uu____2853 -> begin
(

let uu____2856 = (let _0_225 = (let _0_224 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_0_224)))
in (inst_tscheme_with _0_225 insts))
in (match (uu____2856) with
| (uu____2864, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (

let uu____2867 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2867) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| uu____2895 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____2899 -> begin
None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (

let uu____2923 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)
in (match (uu____2923) with
| None -> begin
None
end
| Some (uu____2930, c) -> begin
(

let l = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____2935 = (find l)
in (match (uu____2935) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end)))
end)))
in (

let res = (

let uu____2940 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____2940) with
| Some (l) -> begin
l
end
| None -> begin
(

let uu____2943 = (find l)
in (match (uu____2943) with
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

let uu____2955 = (lookup_qname env l)
in (match (uu____2955) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____2966), uu____2967)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| uu____2982 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____3003 -> (failwith (let _0_227 = (FStar_Util.string_of_int i)
in (let _0_226 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _0_227 _0_226)))))
in (

let uu____3004 = (lookup_datacon env lid)
in (match (uu____3004) with
| (uu____3007, t) -> begin
(

let uu____3009 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3009) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____3011) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____3026 -> begin
(

let b = (FStar_List.nth binders i)
in (let _0_228 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _0_228 Prims.fst)))
end)
end
| uu____3034 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____3041 = (lookup_qname env l)
in (match (uu____3041) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____3050, uu____3051, uu____3052, quals, uu____3054), uu____3055)) -> begin
(FStar_Util.for_some (fun uu___99_3072 -> (match (uu___99_3072) with
| FStar_Syntax_Syntax.Projector (uu____3073) -> begin
true
end
| uu____3076 -> begin
false
end)) quals)
end
| uu____3077 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3092 = (lookup_qname env lid)
in (match (uu____3092) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____3101, uu____3102, uu____3103, uu____3104, uu____3105, uu____3106, uu____3107, uu____3108), uu____3109)) -> begin
true
end
| uu____3128 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3143 = (lookup_qname env lid)
in (match (uu____3143) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3152, uu____3153, uu____3154, uu____3155, uu____3156, uu____3157, tags, uu____3159), uu____3160)) -> begin
(FStar_Util.for_some (fun uu___100_3181 -> (match (uu___100_3181) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3184 -> begin
false
end)) tags)
end
| uu____3185 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3200 = (lookup_qname env lid)
in (match (uu____3200) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_let (uu____3209, uu____3210, uu____3211, tags, uu____3213), uu____3214)) -> begin
(FStar_Util.for_some (fun uu___101_3235 -> (match (uu___101_3235) with
| FStar_Syntax_Syntax.Action (uu____3236) -> begin
true
end
| uu____3237 -> begin
false
end)) tags)
end
| uu____3238 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (

let uu____3255 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in (match (uu____3255) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____3257 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun uu___102_3275 -> (match (uu___102_3275) with
| FStar_Util.Inl (uu____3284) -> begin
Some (false)
end
| FStar_Util.Inr (se, uu____3293) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____3302, uu____3303, uu____3304, qs, uu____3306) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3309) -> begin
Some (true)
end
| uu____3321 -> begin
Some (false)
end)
end))
in (

let uu____3322 = (let _0_229 = (lookup_qname env lid)
in (FStar_Util.bind_opt _0_229 mapper))
in (match (uu____3322) with
| Some (b) -> begin
b
end
| None -> begin
false
end))))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____3348 = (effect_decl_opt env l)
in (match (uu____3348) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_230 = (name_not_found l)
in ((_0_230), ((FStar_Ident.range_of_lid l)))))))
end
| Some (md) -> begin
md
end)))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3397 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3421 -> begin
(

let uu____3422 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____3446 -> (match (uu____3446) with
| (m1, m2, uu____3454, uu____3455, uu____3456) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____3422) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_233 = (let _0_232 = (FStar_Syntax_Print.lid_to_string l1)
in (let _0_231 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _0_232 _0_231)))
in ((_0_233), (env.range))))))
end
| Some (uu____3484, uu____3485, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)))) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end
| uu____3516 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____3532 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))
in (match (uu____3532) with
| None -> begin
(failwith (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str))
end
| Some (md) -> begin
(

let uu____3546 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____3546) with
| (uu____3553, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____3561))::((wp, uu____3563))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____3585 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (Some (res_u)))
end
| uu____3612 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (Some (res_u)))
end
| uu____3613 -> begin
(

let eff_name = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (let _0_236 = (get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_235 = (let _0_234 = (FStar_Syntax_Syntax.as_arg res_t)
in (_0_234)::[])
in ((null_wp), (_0_235)))))) None _0_236))
in (FStar_Syntax_Syntax.mk_Comp (let _0_238 = (let _0_237 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (_0_237)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = _0_238; FStar_Syntax_Syntax.flags = []}))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3636) -> begin
(

let effects = (

let uu___112_3638 = env.effects
in {decls = (ne)::env.effects.decls; order = uu___112_3638.order; joins = uu___112_3638.joins})
in (

let uu___113_3639 = env
in {solver = uu___113_3639.solver; range = uu___113_3639.range; curmodule = uu___113_3639.curmodule; gamma = uu___113_3639.gamma; gamma_cache = uu___113_3639.gamma_cache; modules = uu___113_3639.modules; expected_typ = uu___113_3639.expected_typ; sigtab = uu___113_3639.sigtab; is_pattern = uu___113_3639.is_pattern; instantiate_imp = uu___113_3639.instantiate_imp; effects = effects; generalize = uu___113_3639.generalize; letrecs = uu___113_3639.letrecs; top_level = uu___113_3639.top_level; check_uvars = uu___113_3639.check_uvars; use_eq = uu___113_3639.use_eq; is_iface = uu___113_3639.is_iface; admit = uu___113_3639.admit; lax = uu___113_3639.lax; lax_universes = uu___113_3639.lax_universes; type_of = uu___113_3639.type_of; universe_of = uu___113_3639.universe_of; use_bv_sorts = uu___113_3639.use_bv_sorts; qname_and_index = uu___113_3639.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, uu____3641) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _0_239 = (e1.mlift r wp1)
in (e2.mlift r _0_239)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let uu____3663 = (inst_tscheme lift_t)
in (match (uu____3663) with
| (uu____3668, lift_t) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_243 = (let _0_242 = (FStar_Syntax_Syntax.as_arg r)
in (let _0_241 = (let _0_240 = (FStar_Syntax_Syntax.as_arg wp1)
in (_0_240)::[])
in (_0_242)::_0_241))
in ((lift_t), (_0_243)))))) None wp1.FStar_Syntax_Syntax.pos)
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

let arg = (let _0_244 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _0_244 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _0_245 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _0_245 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Print.term_to_string (l arg wp)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order uu____3721 -> (match (uu____3721) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_246 -> Some (_0_246)))
end
| uu____3730 -> begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _0_250 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____3746 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____3751 -> begin
(

let uu____3752 = (let _0_248 = (find_edge order ((i), (k)))
in (let _0_247 = (find_edge order ((k), (j)))
in ((_0_248), (_0_247))))
in (match (uu____3752) with
| (Some (e1), Some (e2)) -> begin
(let _0_249 = (compose_edges e1 e2)
in (_0_249)::[])
end
| uu____3764 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order _0_250))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in ((FStar_All.pipe_right order (FStar_List.iter (fun edge -> (

let uu____3776 = ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (let _0_251 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right _0_251 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____3776) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_253 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (let _0_252 = (get_range env)
in ((_0_253), (_0_252)))))))
end
| uu____3778 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____3872 = (let _0_255 = (find_edge order ((i), (k)))
in (let _0_254 = (find_edge order ((j), (k)))
in ((_0_255), (_0_254))))
in (match (uu____3872) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, uu____3898, uu____3899) -> begin
(

let uu____3903 = ((FStar_Util.is_some (find_edge order ((k), (ub)))) && (not ((FStar_Util.is_some (find_edge order ((ub), (k)))))))
in (match (uu____3903) with
| true -> begin
Some (((k), (ik), (jk)))
end
| uu____3911 -> begin
bopt
end))
end)
end
| uu____3912 -> begin
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

let uu___114_3991 = env.effects
in {decls = uu___114_3991.decls; order = order; joins = joins})
in (

let uu___115_3992 = env
in {solver = uu___115_3992.solver; range = uu___115_3992.range; curmodule = uu___115_3992.curmodule; gamma = uu___115_3992.gamma; gamma_cache = uu___115_3992.gamma_cache; modules = uu___115_3992.modules; expected_typ = uu___115_3992.expected_typ; sigtab = uu___115_3992.sigtab; is_pattern = uu___115_3992.is_pattern; instantiate_imp = uu___115_3992.instantiate_imp; effects = effects; generalize = uu___115_3992.generalize; letrecs = uu___115_3992.letrecs; top_level = uu___115_3992.top_level; check_uvars = uu___115_3992.check_uvars; use_eq = uu___115_3992.use_eq; is_iface = uu___115_3992.is_iface; admit = uu___115_3992.admit; lax = uu___115_3992.lax; lax_universes = uu___115_3992.lax_universes; type_of = uu___115_3992.type_of; universe_of = uu___115_3992.universe_of; use_bv_sorts = uu___115_3992.use_bv_sorts; qname_and_index = uu___115_3992.qname_and_index})));
))))))))))))
end
| uu____3993 -> begin
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
(let _0_256 = (push x rest)
in (local)::_0_256)
end))
in (

let uu___116_4018 = env
in (let _0_257 = (push s env.gamma)
in {solver = uu___116_4018.solver; range = uu___116_4018.range; curmodule = uu___116_4018.curmodule; gamma = _0_257; gamma_cache = uu___116_4018.gamma_cache; modules = uu___116_4018.modules; expected_typ = uu___116_4018.expected_typ; sigtab = uu___116_4018.sigtab; is_pattern = uu___116_4018.is_pattern; instantiate_imp = uu___116_4018.instantiate_imp; effects = uu___116_4018.effects; generalize = uu___116_4018.generalize; letrecs = uu___116_4018.letrecs; top_level = uu___116_4018.top_level; check_uvars = uu___116_4018.check_uvars; use_eq = uu___116_4018.use_eq; is_iface = uu___116_4018.is_iface; admit = uu___116_4018.admit; lax = uu___116_4018.lax; lax_universes = uu___116_4018.lax_universes; type_of = uu___116_4018.type_of; universe_of = uu___116_4018.universe_of; use_bv_sorts = uu___116_4018.use_bv_sorts; qname_and_index = uu___116_4018.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___117_4044 = env
in {solver = uu___117_4044.solver; range = uu___117_4044.range; curmodule = uu___117_4044.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___117_4044.gamma_cache; modules = uu___117_4044.modules; expected_typ = uu___117_4044.expected_typ; sigtab = uu___117_4044.sigtab; is_pattern = uu___117_4044.is_pattern; instantiate_imp = uu___117_4044.instantiate_imp; effects = uu___117_4044.effects; generalize = uu___117_4044.generalize; letrecs = uu___117_4044.letrecs; top_level = uu___117_4044.top_level; check_uvars = uu___117_4044.check_uvars; use_eq = uu___117_4044.use_eq; is_iface = uu___117_4044.is_iface; admit = uu___117_4044.admit; lax = uu___117_4044.lax; lax_universes = uu___117_4044.lax_universes; type_of = uu___117_4044.type_of; universe_of = uu___117_4044.universe_of; use_bv_sorts = uu___117_4044.use_bv_sorts; qname_and_index = uu___117_4044.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env uu____4060 -> (match (uu____4060) with
| (x, uu____4064) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let x = (

let uu___118_4084 = x
in {FStar_Syntax_Syntax.ppname = uu___118_4084.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_4084.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___119_4114 = env
in {solver = uu___119_4114.solver; range = uu___119_4114.range; curmodule = uu___119_4114.curmodule; gamma = []; gamma_cache = uu___119_4114.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = uu___119_4114.sigtab; is_pattern = uu___119_4114.is_pattern; instantiate_imp = uu___119_4114.instantiate_imp; effects = uu___119_4114.effects; generalize = uu___119_4114.generalize; letrecs = uu___119_4114.letrecs; top_level = uu___119_4114.top_level; check_uvars = uu___119_4114.check_uvars; use_eq = uu___119_4114.use_eq; is_iface = uu___119_4114.is_iface; admit = uu___119_4114.admit; lax = uu___119_4114.lax; lax_universes = uu___119_4114.lax_universes; type_of = uu___119_4114.type_of; universe_of = uu___119_4114.universe_of; use_bv_sorts = uu___119_4114.use_bv_sorts; qname_and_index = uu___119_4114.qname_and_index});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___120_4129 = env
in {solver = uu___120_4129.solver; range = uu___120_4129.range; curmodule = uu___120_4129.curmodule; gamma = uu___120_4129.gamma; gamma_cache = uu___120_4129.gamma_cache; modules = uu___120_4129.modules; expected_typ = Some (t); sigtab = uu___120_4129.sigtab; is_pattern = uu___120_4129.is_pattern; instantiate_imp = uu___120_4129.instantiate_imp; effects = uu___120_4129.effects; generalize = uu___120_4129.generalize; letrecs = uu___120_4129.letrecs; top_level = uu___120_4129.top_level; check_uvars = uu___120_4129.check_uvars; use_eq = false; is_iface = uu___120_4129.is_iface; admit = uu___120_4129.admit; lax = uu___120_4129.lax; lax_universes = uu___120_4129.lax_universes; type_of = uu___120_4129.type_of; universe_of = uu___120_4129.universe_of; use_bv_sorts = uu___120_4129.use_bv_sorts; qname_and_index = uu___120_4129.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _0_258 = (expected_typ env)
in (((

let uu___121_4143 = env
in {solver = uu___121_4143.solver; range = uu___121_4143.range; curmodule = uu___121_4143.curmodule; gamma = uu___121_4143.gamma; gamma_cache = uu___121_4143.gamma_cache; modules = uu___121_4143.modules; expected_typ = None; sigtab = uu___121_4143.sigtab; is_pattern = uu___121_4143.is_pattern; instantiate_imp = uu___121_4143.instantiate_imp; effects = uu___121_4143.effects; generalize = uu___121_4143.generalize; letrecs = uu___121_4143.letrecs; top_level = uu___121_4143.top_level; check_uvars = uu___121_4143.check_uvars; use_eq = false; is_iface = uu___121_4143.is_iface; admit = uu___121_4143.admit; lax = uu___121_4143.lax; lax_universes = uu___121_4143.lax_universes; type_of = uu___121_4143.type_of; universe_of = uu___121_4143.universe_of; use_bv_sorts = uu___121_4143.use_bv_sorts; qname_and_index = uu___121_4143.qname_and_index})), (_0_258))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
(let _0_259 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___103_4158 -> (match (uu___103_4158) with
| Binding_sig (uu____4160, se) -> begin
(se)::[]
end
| uu____4164 -> begin
[]
end))))
in (FStar_All.pipe_right _0_259 FStar_List.rev))
end
| uu____4165 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___122_4167 = env
in {solver = uu___122_4167.solver; range = uu___122_4167.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___122_4167.gamma_cache; modules = (m)::env.modules; expected_typ = uu___122_4167.expected_typ; sigtab = uu___122_4167.sigtab; is_pattern = uu___122_4167.is_pattern; instantiate_imp = uu___122_4167.instantiate_imp; effects = uu___122_4167.effects; generalize = uu___122_4167.generalize; letrecs = uu___122_4167.letrecs; top_level = uu___122_4167.top_level; check_uvars = uu___122_4167.check_uvars; use_eq = uu___122_4167.use_eq; is_iface = uu___122_4167.is_iface; admit = uu___122_4167.admit; lax = uu___122_4167.lax; lax_universes = uu___122_4167.lax_universes; type_of = uu___122_4167.type_of; universe_of = uu___122_4167.universe_of; use_bv_sorts = uu___122_4167.use_bv_sorts; qname_and_index = uu___122_4167.qname_and_index});
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
| (Binding_univ (uu____4217))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _0_261 = (let _0_260 = (FStar_Syntax_Free.uvars t)
in (ext out _0_260))
in (aux _0_261 tl))
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
(let _0_263 = (let _0_262 = (FStar_Syntax_Free.univs t)
in (ext out _0_262))
in (aux _0_263 tl))
end
| (Binding_sig (uu____4284))::uu____4285 -> begin
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
| (Binding_sig_inst (uu____4322))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(let _0_264 = (FStar_Util.set_add uname out)
in (aux _0_264 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _0_266 = (let _0_265 = (FStar_Syntax_Free.univnames t)
in (ext out _0_265))
in (aux _0_266 tl))
end
| (Binding_sig (uu____4344))::uu____4345 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___104_4361 -> (match (uu___104_4361) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _0_268 = (let _0_267 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _0_267 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _0_268 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___105_4422 -> (match (uu___105_4422) with
| Binding_sig (lids, uu____4426) -> begin
(FStar_List.append lids keys)
end
| uu____4429 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____4431 v keys -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)) keys)))


let dummy_solver : solver_t = {init = (fun uu____4435 -> ()); push = (fun uu____4436 -> ()); pop = (fun uu____4437 -> ()); mark = (fun uu____4438 -> ()); reset_mark = (fun uu____4439 -> ()); commit_mark = (fun uu____4440 -> ()); encode_modul = (fun uu____4441 uu____4442 -> ()); encode_sig = (fun uu____4443 uu____4444 -> ()); solve = (fun uu____4445 uu____4446 uu____4447 -> ()); is_trivial = (fun uu____4451 uu____4452 -> false); finish = (fun uu____4453 -> ()); refresh = (fun uu____4454 -> ())}




