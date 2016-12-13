
open Prims

type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)


let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_lid = (fun _discr_ -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_sig = (fun _discr_ -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_univ = (fun _discr_ -> (match (_discr_) with
| Binding_univ (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_sig_inst = (fun _discr_ -> (match (_discr_) with
| Binding_sig_inst (_) -> begin
true
end
| _ -> begin
false
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_52_15) -> begin
_52_15
end))


let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_52_18) -> begin
_52_18
end))


let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_52_21) -> begin
_52_21
end))


let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_52_24) -> begin
_52_24
end))


let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_52_27) -> begin
_52_27
end))


type delta_level =
| NoDelta
| Inlining
| Eager_unfolding_only
| Unfold of FStar_Syntax_Syntax.delta_depth


let is_NoDelta = (fun _discr_ -> (match (_discr_) with
| NoDelta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inlining = (fun _discr_ -> (match (_discr_) with
| Inlining (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eager_unfolding_only = (fun _discr_ -> (match (_discr_) with
| Eager_unfolding_only (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unfold = (fun _discr_ -> (match (_discr_) with
| Unfold (_) -> begin
true
end
| _ -> begin
false
end))


let ___Unfold____0 = (fun projectee -> (match (projectee) with
| Unfold (_52_30) -> begin
_52_30
end))


type mlift =
FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ


type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ}


let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))


type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))


type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either


type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) Prims.option} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; stsize : Prims.unit  ->  Prims.int; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))


let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))


type env_t =
env


type implicits =
(env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list


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
| _52_108 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun _52_109 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _52_110 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _147_431 = (new_gamma_cache ())
in (let _147_430 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _147_431; modules = []; expected_typ = None; sigtab = _147_430; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun _52_126 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| [] -> begin
(FStar_All.failwith "Empty query indices!")
end
| _52_129 -> begin
(let _147_496 = (let _147_495 = (let _147_493 = (FStar_ST.read query_indices)
in (FStar_List.hd _147_493))
in (let _147_494 = (FStar_ST.read query_indices)
in (_147_495)::_147_494))
in (FStar_ST.op_Colon_Equals query_indices _147_496))
end)
end))
in (

let pop_query_indices = (fun _52_131 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| [] -> begin
(FStar_All.failwith "Empty query indices!")
end
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices tl)
end)
end))
in (

let add_query_index = (fun _52_139 -> (match (_52_139) with
| (l, n) -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n)))::hd)::tl))
end
| _52_144 -> begin
(FStar_All.failwith "Empty query indices")
end)
end))
in (

let peek_query_indices = (fun _52_146 -> (match (()) with
| () -> begin
(let _147_503 = (FStar_ST.read query_indices)
in (FStar_List.hd _147_503))
end))
in (

let commit_query_index_mark = (fun _52_148 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::(_52_151)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices ((hd)::tl))
end
| _52_156 -> begin
(FStar_All.failwith "Unmarked query index stack")
end)
end))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> (

let _52_160 = (let _147_509 = (let _147_508 = (FStar_ST.read stack)
in (env)::_147_508)
in (FStar_ST.op_Colon_Equals stack _147_509))
in (

let _52_162 = env
in (let _147_511 = (FStar_Util.smap_copy (gamma_cache env))
in (let _147_510 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_162.solver; range = _52_162.range; curmodule = _52_162.curmodule; gamma = _52_162.gamma; gamma_cache = _147_511; modules = _52_162.modules; expected_typ = _52_162.expected_typ; sigtab = _147_510; is_pattern = _52_162.is_pattern; instantiate_imp = _52_162.instantiate_imp; effects = _52_162.effects; generalize = _52_162.generalize; letrecs = _52_162.letrecs; top_level = _52_162.top_level; check_uvars = _52_162.check_uvars; use_eq = _52_162.use_eq; is_iface = _52_162.is_iface; admit = _52_162.admit; lax = _52_162.lax; lax_universes = _52_162.lax_universes; type_of = _52_162.type_of; universe_of = _52_162.universe_of; use_bv_sorts = _52_162.use_bv_sorts; qname_and_index = _52_162.qname_and_index})))))
in (

let pop_stack = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_169 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_172 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let push = (fun env -> (

let _52_175 = (push_query_indices ())
in (push_stack env)))
in (

let pop = (fun env -> (

let _52_179 = (pop_query_indices ())
in (pop_stack env)))
in (

let mark = (fun env -> (

let _52_183 = (push_query_indices ())
in (push_stack env)))
in (

let commit_mark = (fun env -> (

let _52_187 = (commit_query_index_mark ())
in (

let _52_189 = (let _147_522 = (pop_stack env)
in (Prims.ignore _147_522))
in env)))
in (

let reset_mark = (fun env -> (

let _52_193 = (pop_query_indices ())
in (pop_stack env)))
in (

let incr_query_index = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(match ((FStar_All.pipe_right qix (FStar_List.tryFind (fun _52_206 -> (match (_52_206) with
| (m, _52_205) -> begin
(FStar_Ident.lid_equals l m)
end))))) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in (

let _52_209 = (add_query_index ((l), (next)))
in (

let _52_211 = env
in {solver = _52_211.solver; range = _52_211.range; curmodule = _52_211.curmodule; gamma = _52_211.gamma; gamma_cache = _52_211.gamma_cache; modules = _52_211.modules; expected_typ = _52_211.expected_typ; sigtab = _52_211.sigtab; is_pattern = _52_211.is_pattern; instantiate_imp = _52_211.instantiate_imp; effects = _52_211.effects; generalize = _52_211.generalize; letrecs = _52_211.letrecs; top_level = _52_211.top_level; check_uvars = _52_211.check_uvars; use_eq = _52_211.use_eq; is_iface = _52_211.is_iface; admit = _52_211.admit; lax = _52_211.lax; lax_universes = _52_211.lax_universes; type_of = _52_211.type_of; universe_of = _52_211.universe_of; use_bv_sorts = _52_211.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end
| Some (_52_214, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in (

let _52_219 = (add_query_index ((l), (next)))
in (

let _52_221 = env
in {solver = _52_221.solver; range = _52_221.range; curmodule = _52_221.curmodule; gamma = _52_221.gamma; gamma_cache = _52_221.gamma_cache; modules = _52_221.modules; expected_typ = _52_221.expected_typ; sigtab = _52_221.sigtab; is_pattern = _52_221.is_pattern; instantiate_imp = _52_221.instantiate_imp; effects = _52_221.effects; generalize = _52_221.generalize; letrecs = _52_221.letrecs; top_level = _52_221.top_level; check_uvars = _52_221.check_uvars; use_eq = _52_221.use_eq; is_iface = _52_221.is_iface; admit = _52_221.admit; lax = _52_221.lax; lax_universes = _52_221.lax_universes; type_of = _52_221.type_of; universe_of = _52_221.universe_of; use_bv_sorts = _52_221.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end)
end)))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop; es_incr_query_index = incr_query_index})))))))))))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_225 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_228 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_231 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_234 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_238 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let incr_query_index : env  ->  env = (fun env -> (stack_ops.es_incr_query_index env))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_245 = e
in {solver = _52_245.solver; range = r; curmodule = _52_245.curmodule; gamma = _52_245.gamma; gamma_cache = _52_245.gamma_cache; modules = _52_245.modules; expected_typ = _52_245.expected_typ; sigtab = _52_245.sigtab; is_pattern = _52_245.is_pattern; instantiate_imp = _52_245.instantiate_imp; effects = _52_245.effects; generalize = _52_245.generalize; letrecs = _52_245.letrecs; top_level = _52_245.top_level; check_uvars = _52_245.check_uvars; use_eq = _52_245.use_eq; is_iface = _52_245.is_iface; admit = _52_245.admit; lax = _52_245.lax; lax_universes = _52_245.lax_universes; type_of = _52_245.type_of; universe_of = _52_245.universe_of; use_bv_sorts = _52_245.use_bv_sorts; qname_and_index = _52_245.qname_and_index})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_252 = env
in {solver = _52_252.solver; range = _52_252.range; curmodule = lid; gamma = _52_252.gamma; gamma_cache = _52_252.gamma_cache; modules = _52_252.modules; expected_typ = _52_252.expected_typ; sigtab = _52_252.sigtab; is_pattern = _52_252.is_pattern; instantiate_imp = _52_252.instantiate_imp; effects = _52_252.effects; generalize = _52_252.generalize; letrecs = _52_252.letrecs; top_level = _52_252.top_level; check_uvars = _52_252.check_uvars; use_eq = _52_252.use_eq; is_iface = _52_252.is_iface; admit = _52_252.admit; lax = _52_252.lax; lax_universes = _52_252.lax_universes; type_of = _52_252.type_of; universe_of = _52_252.universe_of; use_bv_sorts = _52_252.use_bv_sorts; qname_and_index = _52_252.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _147_575 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _147_575)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _52_261 -> (match (()) with
| () -> begin
(let _147_578 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_147_578))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _52_273) -> begin
(

let _52_275 = ()
in (

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _147_585 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_147_585))))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_288 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let _52_295 = (inst_tscheme t)
in (match (_52_295) with
| (us, t) -> begin
(let _147_593 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (_147_593)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_301 -> (match (_52_301) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_304 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _147_606 = (let _147_605 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _147_604 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _147_603 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _147_602 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _147_605 _147_604 _147_603 _147_602)))))
in (FStar_All.failwith _147_606))
end else begin
()
end
in (let _147_607 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _147_607))))
end
| _52_307 -> begin
(let _147_609 = (let _147_608 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _147_608))
in (FStar_All.failwith _147_609))
end)
end))


type tri =
| Yes
| No
| Maybe


let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))


let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))


let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match (((c), (l))) with
| ([], _52_318) -> begin
Maybe
end
| (_52_321, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_332 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))


let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let cache = (fun t -> (

let _52_338 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _147_629 = (let _147_628 = (inst_tscheme t)
in FStar_Util.Inl (_147_628))
in Some (_147_629))
end else begin
None
end
end
| Binding_sig (_52_347, FStar_Syntax_Syntax.Sig_bundle (ses, _52_350, _52_352, _52_354)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _147_631 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _147_631 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr (((se), (None)))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_367) -> begin
Some (t)
end
| _52_370 -> begin
(cache t)
end))
in if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
(maybe_cache (FStar_Util.Inr (((s), (None)))))
end else begin
None
end)
end
| Binding_sig_inst (lids, s, us) -> begin
if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
Some (FStar_Util.Inr (((s), (Some (us)))))
end else begin
None
end
end
| _52_377 -> begin
None
end)))
end
| se -> begin
se
end)
end else begin
None
end
in if (FStar_Util.is_some found) then begin
found
end else begin
if ((cur_mod <> Yes) || (has_interface env env.curmodule)) then begin
(match ((find_in_sigtab env lid)) with
| Some (se) -> begin
Some (FStar_Util.Inr (((se), (None))))
end
| None -> begin
None
end)
end else begin
None
end
end))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_387, _52_389, _52_391) -> begin
(add_sigelts env ses)
end
| _52_395 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let _52_398 = (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_402) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| _52_408 -> begin
()
end)))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_3 -> (match (_52_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_417 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_421, (lb)::[]), _52_426, _52_428, _52_430) -> begin
(let _147_653 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_147_653))
end
| FStar_Syntax_Syntax.Sig_let ((_52_434, lbs), _52_438, _52_440, _52_442) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_447) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _147_655 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_147_655))
end else begin
None
end
end)))
end
| _52_452 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_456) -> begin
(let _147_661 = (let _147_660 = (let _147_659 = (let _147_658 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _147_658))
in ((ne.FStar_Syntax_Syntax.univs), (_147_659)))
in (inst_tscheme _147_660))
in Some (_147_661))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_463, _52_465, _52_467, _52_469) -> begin
(let _147_665 = (let _147_664 = (let _147_663 = (let _147_662 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _147_662))
in ((us), (_147_663)))
in (inst_tscheme _147_664))
in Some (_147_665))
end
| _52_473 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun _52_4 -> (match (_52_4) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_480, uvs, t, _52_484, _52_486, _52_488, _52_490, _52_492), None) -> begin
(let _147_672 = (inst_tscheme ((uvs), (t)))
in Some (_147_672))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_503), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _147_673 = (inst_tscheme ((uvs), (t)))
in Some (_147_673))
end else begin
None
end
end else begin
(let _147_674 = (inst_tscheme ((uvs), (t)))
in Some (_147_674))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_514, _52_516, _52_518, _52_520), None) -> begin
(match (tps) with
| [] -> begin
(let _147_676 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _147_675 -> Some (_147_675)) _147_676))
end
| _52_528 -> begin
(let _147_681 = (let _147_680 = (let _147_679 = (let _147_678 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _147_678))
in ((uvs), (_147_679)))
in (inst_tscheme _147_680))
in (FStar_All.pipe_left (fun _147_677 -> Some (_147_677)) _147_681))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_534, _52_536, _52_538, _52_540), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _147_683 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _147_682 -> Some (_147_682)) _147_683))
end
| _52_549 -> begin
(let _147_688 = (let _147_687 = (let _147_686 = (let _147_685 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _147_685))
in ((uvs), (_147_686)))
in (inst_tscheme_with _147_687 us))
in (FStar_All.pipe_left (fun _147_684 -> Some (_147_684)) _147_688))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_553), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_558 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _147_689 = (lookup_qname env lid)
in (FStar_Util.bind_opt _147_689 mapper))) with
| Some (us, t) -> begin
Some (((us), ((

let _52_564 = t
in {FStar_Syntax_Syntax.n = _52_564.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_564.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_564.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end)))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_52_571) -> begin
true
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _147_701 = (let _147_700 = (let _147_699 = (variable_not_found bv)
in (let _147_698 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_147_699), (_147_698))))
in FStar_Syntax_Syntax.Error (_147_700))
in (Prims.raise _147_701))
end
| Some (t) -> begin
(let _147_702 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range _147_702 t))
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (match ((try_lookup_lid_aux env l)) with
| None -> begin
None
end
| Some (us, t) -> begin
(let _147_708 = (let _147_707 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (_147_707)))
in Some (_147_708))
end))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _147_715 = (let _147_714 = (let _147_713 = (name_not_found l)
in ((_147_713), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_147_714))
in (Prims.raise _147_715))
end
| Some (us, t) -> begin
((us), (t))
end))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_5 -> (match (_52_5) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_598 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_602, uvs, t, q, _52_607), None)) -> begin
(let _147_730 = (let _147_729 = (let _147_728 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (_147_728)))
in ((_147_729), (q)))
in Some (_147_730))
end
| _52_615 -> begin
None
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_619, uvs, t, _52_623, _52_625), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| _52_633 -> begin
(let _147_737 = (let _147_736 = (let _147_735 = (name_not_found lid)
in ((_147_735), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_147_736))
in (Prims.raise _147_737))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_637, uvs, t, _52_641, _52_643, _52_645, _52_647, _52_649), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| _52_657 -> begin
(let _147_744 = (let _147_743 = (let _147_742 = (name_not_found lid)
in ((_147_742), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_147_743))
in (Prims.raise _147_744))
end))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_661, _52_663, _52_665, _52_667, _52_669, dcs, _52_672, _52_674), _52_678)) -> begin
dcs
end
| _52_683 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_687, _52_689, _52_691, l, _52_694, _52_696, _52_698, _52_700), _52_704)) -> begin
l
end
| _52_709 -> begin
(let _147_754 = (let _147_753 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _147_753))
in (FStar_All.failwith _147_754))
end))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_722, lbs), _52_726, _52_728, quals) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _147_767 = (let _147_766 = (let _147_765 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) _147_765))
in ((lb.FStar_Syntax_Syntax.lbunivs), (_147_766)))
in Some (_147_767))
end else begin
None
end)))
end
| _52_735 -> begin
None
end)
end
| _52_737 -> begin
None
end)))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_747, t) -> begin
(let _147_772 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (_147_772))
end)
end
| _52_752 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _147_779 = (let _147_778 = (let _147_777 = (name_not_found ftv)
in ((_147_777), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_147_778))
in (Prims.raise _147_779))
end
| Some (k) -> begin
k
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (match ((lookup_qname env lid0)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_767, _52_769), None)) -> begin
(

let lid = (let _147_786 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid _147_786))
in if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_6 -> (match (_52_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_780 -> begin
false
end)))) then begin
None
end else begin
(

let insts = if ((FStar_List.length univ_insts) = (FStar_List.length univs)) then begin
univ_insts
end else begin
if ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) && ((FStar_List.length univ_insts) = (Prims.parse_int "1"))) then begin
(FStar_List.append univ_insts ((FStar_Syntax_Syntax.U_zero)::[]))
end else begin
(let _147_790 = (let _147_789 = (FStar_Syntax_Print.lid_to_string lid)
in (let _147_788 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" _147_789 _147_788)))
in (FStar_All.failwith _147_790))
end
end
in (match (((binders), (univs))) with
| ([], _52_784) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_787, (_52_794)::(_52_791)::_52_789) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _147_793 = (let _147_792 = (FStar_Syntax_Print.lid_to_string lid)
in (let _147_791 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _147_792 _147_791)))
in (FStar_All.failwith _147_793))
end
| _52_798 -> begin
(

let _52_802 = (let _147_795 = (let _147_794 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_147_794)))
in (inst_tscheme_with _147_795 insts))
in (match (_52_802) with
| (_52_800, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (match ((let _147_796 = (FStar_Syntax_Subst.compress t)
in _147_796.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| _52_809 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))
end)
end
| _52_811 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)) with
| None -> begin
None
end
| Some (_52_819, c) -> begin
(

let l = (FStar_Syntax_Util.comp_effect_name c)
in (match ((find l)) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end))
end))
in (

let res = (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(match ((find l)) with
| None -> begin
l
end
| Some (m) -> begin
(

let _52_833 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in (FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l))))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l = (norm_eff_name env l)
in (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, _52_841), _52_845)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| _52_850 -> begin
[]
end)))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_855 -> (match (()) with
| () -> begin
(let _147_817 = (let _147_816 = (FStar_Util.string_of_int i)
in (let _147_815 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _147_816 _147_815)))
in (FStar_All.failwith _147_817))
end))
in (

let _52_859 = (lookup_datacon env lid)
in (match (_52_859) with
| (_52_857, t) -> begin
(match ((let _147_818 = (FStar_Syntax_Subst.compress t)
in _147_818.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_862) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _147_819 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _147_819 Prims.fst)))
end
end
| _52_867 -> begin
(fail ())
end)
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_871, _52_873, _52_875, quals, _52_878), _52_882)) -> begin
(FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Projector (_52_888) -> begin
true
end
| _52_891 -> begin
false
end)) quals)
end
| _52_893 -> begin
false
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_897, _52_899, _52_901, _52_903, _52_905, _52_907, _52_909, _52_911), _52_915)) -> begin
true
end
| _52_920 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_924, _52_926, _52_928, _52_930, _52_932, _52_934, tags, _52_937), _52_941)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_953 -> begin
false
end)) tags)
end
| _52_955 -> begin
false
end))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (match ((let _147_838 = (FStar_Syntax_Util.un_uinst head)
in _147_838.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_962 -> begin
false
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_9 -> (match (_52_9) with
| FStar_Util.Inl (_52_967) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_971) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_975, _52_977, _52_979, qs, _52_982) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_986) -> begin
Some (true)
end
| _52_989 -> begin
Some (false)
end)
end))
in (match ((let _147_845 = (lookup_qname env lid)
in (FStar_Util.bind_opt _147_845 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _147_857 = (let _147_856 = (let _147_855 = (name_not_found l)
in ((_147_855), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_147_856))
in (Prims.raise _147_857))
end
| Some (md) -> begin
md
end))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
((FStar_Syntax_Const.effect_GTot_lid), ((fun t wp -> wp)), ((fun t wp -> wp)))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_1021 -> (match (_52_1021) with
| (m1, m2, _52_1016, _52_1018, _52_1020) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _147_933 = (let _147_932 = (let _147_931 = (let _147_930 = (FStar_Syntax_Print.lid_to_string l1)
in (let _147_929 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _147_930 _147_929)))
in ((_147_931), (env.range)))
in FStar_Syntax_Syntax.Error (_147_932))
in (Prims.raise _147_933))
end
| Some (_52_1024, _52_1026, m3, j1, j2) -> begin
((m3), (j1), (j2))
end)
end
end)


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)


let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _147_948 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _147_948))
end
| Some (md) -> begin
(

let _52_1047 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_52_1047) with
| (_52_1045, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_1056))::((wp, _52_1052))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _52_1064 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_1071) -> begin
(

let effects = (

let _52_1074 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1074.order; joins = _52_1074.joins})
in (

let _52_1077 = env
in {solver = _52_1077.solver; range = _52_1077.range; curmodule = _52_1077.curmodule; gamma = _52_1077.gamma; gamma_cache = _52_1077.gamma_cache; modules = _52_1077.modules; expected_typ = _52_1077.expected_typ; sigtab = _52_1077.sigtab; is_pattern = _52_1077.is_pattern; instantiate_imp = _52_1077.instantiate_imp; effects = effects; generalize = _52_1077.generalize; letrecs = _52_1077.letrecs; top_level = _52_1077.top_level; check_uvars = _52_1077.check_uvars; use_eq = _52_1077.use_eq; is_iface = _52_1077.is_iface; admit = _52_1077.admit; lax = _52_1077.lax; lax_universes = _52_1077.lax_universes; type_of = _52_1077.type_of; universe_of = _52_1077.universe_of; use_bv_sorts = _52_1077.use_bv_sorts; qname_and_index = _52_1077.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1081) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _147_963 = (e1.mlift r wp1)
in (e2.mlift r _147_963)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1096 = (inst_tscheme lift_t)
in (match (_52_1096) with
| (_52_1094, lift_t) -> begin
(let _147_975 = (let _147_974 = (let _147_973 = (let _147_972 = (FStar_Syntax_Syntax.as_arg r)
in (let _147_971 = (let _147_970 = (FStar_Syntax_Syntax.as_arg wp1)
in (_147_970)::[])
in (_147_972)::_147_971))
in ((lift_t), (_147_973)))
in FStar_Syntax_Syntax.Tm_app (_147_974))
in (FStar_Syntax_Syntax.mk _147_975 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_lift_wp = (match (sub.FStar_Syntax_Syntax.lift_wp) with
| Some (sub_lift_wp) -> begin
sub_lift_wp
end
| None -> begin
(FStar_All.failwith "sub effect should\'ve been elaborated at this stage")
end)
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub_lift_wp)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _147_992 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _147_992 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _147_993 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _147_993 FStar_Syntax_Syntax.Delta_constant None))
in (let _147_994 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _147_994)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1117 -> (match (_52_1117) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _147_1000 -> Some (_147_1000)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _147_1008 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _147_1007 = (find_edge order ((i), (k)))
in (let _147_1006 = (find_edge order ((k), (j)))
in ((_147_1007), (_147_1006))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1129 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _147_1008))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let _52_1135 = (FStar_All.pipe_right order (FStar_List.iter (fun edge -> if ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (let _147_1012 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right _147_1012 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))) then begin
(let _147_1016 = (let _147_1015 = (let _147_1014 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (let _147_1013 = (get_range env)
in ((_147_1014), (_147_1013))))
in FStar_Syntax_Syntax.Error (_147_1015))
in (Prims.raise _147_1016))
end else begin
()
end)))
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _147_1106 = (find_edge order ((i), (k)))
in (let _147_1105 = (find_edge order ((j), (k)))
in ((_147_1106), (_147_1105))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _52_1149, _52_1151) -> begin
if ((let _147_1107 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _147_1107)) && (not ((let _147_1108 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _147_1108))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _52_1155 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let _52_1164 = env.effects
in {decls = _52_1164.decls; order = order; joins = joins})
in (

let _52_1167 = env
in {solver = _52_1167.solver; range = _52_1167.range; curmodule = _52_1167.curmodule; gamma = _52_1167.gamma; gamma_cache = _52_1167.gamma_cache; modules = _52_1167.modules; expected_typ = _52_1167.expected_typ; sigtab = _52_1167.sigtab; is_pattern = _52_1167.is_pattern; instantiate_imp = _52_1167.instantiate_imp; effects = effects; generalize = _52_1167.generalize; letrecs = _52_1167.letrecs; top_level = _52_1167.top_level; check_uvars = _52_1167.check_uvars; use_eq = _52_1167.use_eq; is_iface = _52_1167.is_iface; admit = _52_1167.admit; lax = _52_1167.lax; lax_universes = _52_1167.lax_universes; type_of = _52_1167.type_of; universe_of = _52_1167.universe_of; use_bv_sorts = _52_1167.use_bv_sorts; qname_and_index = _52_1167.qname_and_index})))))))))))))))
end
| _52_1170 -> begin
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
(let _147_1157 = (push x rest)
in (local)::_147_1157)
end))
in (

let _52_1192 = env
in (let _147_1158 = (push s env.gamma)
in {solver = _52_1192.solver; range = _52_1192.range; curmodule = _52_1192.curmodule; gamma = _147_1158; gamma_cache = _52_1192.gamma_cache; modules = _52_1192.modules; expected_typ = _52_1192.expected_typ; sigtab = _52_1192.sigtab; is_pattern = _52_1192.is_pattern; instantiate_imp = _52_1192.instantiate_imp; effects = _52_1192.effects; generalize = _52_1192.generalize; letrecs = _52_1192.letrecs; top_level = _52_1192.top_level; check_uvars = _52_1192.check_uvars; use_eq = _52_1192.use_eq; is_iface = _52_1192.is_iface; admit = _52_1192.admit; lax = _52_1192.lax; lax_universes = _52_1192.lax_universes; type_of = _52_1192.type_of; universe_of = _52_1192.universe_of; use_bv_sorts = _52_1192.use_bv_sorts; qname_and_index = _52_1192.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (let _147_1165 = (let _147_1164 = (let _147_1163 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_147_1163), (s)))
in Binding_sig (_147_1164))
in (push_in_gamma env _147_1165))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (let _147_1174 = (let _147_1173 = (let _147_1172 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_147_1172), (s), (us)))
in Binding_sig_inst (_147_1173))
in (push_in_gamma env _147_1174))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1203 = env
in {solver = _52_1203.solver; range = _52_1203.range; curmodule = _52_1203.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1203.gamma_cache; modules = _52_1203.modules; expected_typ = _52_1203.expected_typ; sigtab = _52_1203.sigtab; is_pattern = _52_1203.is_pattern; instantiate_imp = _52_1203.instantiate_imp; effects = _52_1203.effects; generalize = _52_1203.generalize; letrecs = _52_1203.letrecs; top_level = _52_1203.top_level; check_uvars = _52_1203.check_uvars; use_eq = _52_1203.use_eq; is_iface = _52_1203.is_iface; admit = _52_1203.admit; lax = _52_1203.lax; lax_universes = _52_1203.lax_universes; type_of = _52_1203.type_of; universe_of = _52_1203.universe_of; use_bv_sorts = _52_1203.use_bv_sorts; qname_and_index = _52_1203.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1213 -> (match (_52_1213) with
| (x, _52_1212) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1218 = ()
in (

let x = (

let _52_1220 = x
in {FStar_Syntax_Syntax.ppname = _52_1220.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1220.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1230 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1232 = env
in {solver = _52_1232.solver; range = _52_1232.range; curmodule = _52_1232.curmodule; gamma = []; gamma_cache = _52_1232.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1232.sigtab; is_pattern = _52_1232.is_pattern; instantiate_imp = _52_1232.instantiate_imp; effects = _52_1232.effects; generalize = _52_1232.generalize; letrecs = _52_1232.letrecs; top_level = _52_1232.top_level; check_uvars = _52_1232.check_uvars; use_eq = _52_1232.use_eq; is_iface = _52_1232.is_iface; admit = _52_1232.admit; lax = _52_1232.lax; lax_universes = _52_1232.lax_universes; type_of = _52_1232.type_of; universe_of = _52_1232.universe_of; use_bv_sorts = _52_1232.use_bv_sorts; qname_and_index = _52_1232.qname_and_index})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1240 = env
in {solver = _52_1240.solver; range = _52_1240.range; curmodule = _52_1240.curmodule; gamma = _52_1240.gamma; gamma_cache = _52_1240.gamma_cache; modules = _52_1240.modules; expected_typ = Some (t); sigtab = _52_1240.sigtab; is_pattern = _52_1240.is_pattern; instantiate_imp = _52_1240.instantiate_imp; effects = _52_1240.effects; generalize = _52_1240.generalize; letrecs = _52_1240.letrecs; top_level = _52_1240.top_level; check_uvars = _52_1240.check_uvars; use_eq = false; is_iface = _52_1240.is_iface; admit = _52_1240.admit; lax = _52_1240.lax; lax_universes = _52_1240.lax_universes; type_of = _52_1240.type_of; universe_of = _52_1240.universe_of; use_bv_sorts = _52_1240.use_bv_sorts; qname_and_index = _52_1240.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _147_1217 = (expected_typ env)
in (((

let _52_1247 = env
in {solver = _52_1247.solver; range = _52_1247.range; curmodule = _52_1247.curmodule; gamma = _52_1247.gamma; gamma_cache = _52_1247.gamma_cache; modules = _52_1247.modules; expected_typ = None; sigtab = _52_1247.sigtab; is_pattern = _52_1247.is_pattern; instantiate_imp = _52_1247.instantiate_imp; effects = _52_1247.effects; generalize = _52_1247.generalize; letrecs = _52_1247.letrecs; top_level = _52_1247.top_level; check_uvars = _52_1247.check_uvars; use_eq = false; is_iface = _52_1247.is_iface; admit = _52_1247.admit; lax = _52_1247.lax; lax_universes = _52_1247.lax_universes; type_of = _52_1247.type_of; universe_of = _52_1247.universe_of; use_bv_sorts = _52_1247.use_bv_sorts; qname_and_index = _52_1247.qname_and_index})), (_147_1217))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _147_1223 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1254, se) -> begin
(se)::[]
end
| _52_1259 -> begin
[]
end))))
in (FStar_All.pipe_right _147_1223 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1261 = (add_sigelts env sigs)
in (

let _52_1263 = env
in {solver = _52_1263.solver; range = _52_1263.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1263.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1263.expected_typ; sigtab = _52_1263.sigtab; is_pattern = _52_1263.is_pattern; instantiate_imp = _52_1263.instantiate_imp; effects = _52_1263.effects; generalize = _52_1263.generalize; letrecs = _52_1263.letrecs; top_level = _52_1263.top_level; check_uvars = _52_1263.check_uvars; use_eq = _52_1263.use_eq; is_iface = _52_1263.is_iface; admit = _52_1263.admit; lax = _52_1263.lax; lax_universes = _52_1263.lax_universes; type_of = _52_1263.type_of; universe_of = _52_1263.universe_of; use_bv_sorts = _52_1263.use_bv_sorts; qname_and_index = _52_1263.qname_and_index})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1276))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _147_1235 = (let _147_1234 = (FStar_Syntax_Free.uvars t)
in (ext out _147_1234))
in (aux _147_1235 tl))
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
(let _147_1247 = (let _147_1246 = (FStar_Syntax_Free.univs t)
in (ext out _147_1246))
in (aux _147_1247 tl))
end
| (Binding_sig (_52_1346))::_52_1344 -> begin
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
| (Binding_sig_inst (_52_1360))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(let _147_1258 = (FStar_Util.set_add uname out)
in (aux _147_1258 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _147_1260 = (let _147_1259 = (FStar_Syntax_Free.univnames t)
in (ext out _147_1259))
in (aux _147_1260 tl))
end
| (Binding_sig (_52_1387))::_52_1385 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _52_11 -> (match (_52_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _147_1267 = (let _147_1266 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _147_1266 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _147_1267 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1419) -> begin
(FStar_List.append lids keys)
end
| _52_1423 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1425 v keys -> (let _147_1290 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _147_1290 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1429 -> ()); push = (fun _52_1431 -> ()); pop = (fun _52_1433 -> ()); stsize = (fun _52_1435 -> (Prims.parse_int "0")); mark = (fun _52_1437 -> ()); reset_mark = (fun _52_1439 -> ()); commit_mark = (fun _52_1441 -> ()); encode_modul = (fun _52_1443 _52_1445 -> ()); encode_sig = (fun _52_1447 _52_1449 -> ()); solve = (fun _52_1451 _52_1453 _52_1455 -> ()); is_trivial = (fun _52_1457 _52_1459 -> false); finish = (fun _52_1461 -> ()); refresh = (fun _52_1462 -> ())}




