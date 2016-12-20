
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
| Binding_var (_53_15) -> begin
_53_15
end))


let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_53_18) -> begin
_53_18
end))


let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_53_21) -> begin
_53_21
end))


let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_53_24) -> begin
_53_24
end))


let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_53_27) -> begin
_53_27
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
| Unfold (_53_30) -> begin
_53_30
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
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
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
| _53_107 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun _53_108 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _53_109 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _150_422 = (new_gamma_cache ())
in (let _150_421 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _150_422; modules = []; expected_typ = None; sigtab = _150_421; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun _53_125 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| [] -> begin
(FStar_All.failwith "Empty query indices!")
end
| _53_128 -> begin
(let _150_487 = (let _150_486 = (let _150_484 = (FStar_ST.read query_indices)
in (FStar_List.hd _150_484))
in (let _150_485 = (FStar_ST.read query_indices)
in (_150_486)::_150_485))
in (FStar_ST.op_Colon_Equals query_indices _150_487))
end)
end))
in (

let pop_query_indices = (fun _53_130 -> (match (()) with
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

let add_query_index = (fun _53_138 -> (match (_53_138) with
| (l, n) -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n)))::hd)::tl))
end
| _53_143 -> begin
(FStar_All.failwith "Empty query indices")
end)
end))
in (

let peek_query_indices = (fun _53_145 -> (match (()) with
| () -> begin
(let _150_494 = (FStar_ST.read query_indices)
in (FStar_List.hd _150_494))
end))
in (

let commit_query_index_mark = (fun _53_147 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::(_53_150)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices ((hd)::tl))
end
| _53_155 -> begin
(FStar_All.failwith "Unmarked query index stack")
end)
end))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> (

let _53_159 = (let _150_500 = (let _150_499 = (FStar_ST.read stack)
in (env)::_150_499)
in (FStar_ST.op_Colon_Equals stack _150_500))
in (

let _53_161 = env
in (let _150_502 = (FStar_Util.smap_copy (gamma_cache env))
in (let _150_501 = (FStar_Util.smap_copy (sigtab env))
in {solver = _53_161.solver; range = _53_161.range; curmodule = _53_161.curmodule; gamma = _53_161.gamma; gamma_cache = _150_502; modules = _53_161.modules; expected_typ = _53_161.expected_typ; sigtab = _150_501; is_pattern = _53_161.is_pattern; instantiate_imp = _53_161.instantiate_imp; effects = _53_161.effects; generalize = _53_161.generalize; letrecs = _53_161.letrecs; top_level = _53_161.top_level; check_uvars = _53_161.check_uvars; use_eq = _53_161.use_eq; is_iface = _53_161.is_iface; admit = _53_161.admit; lax = _53_161.lax; lax_universes = _53_161.lax_universes; type_of = _53_161.type_of; universe_of = _53_161.universe_of; use_bv_sorts = _53_161.use_bv_sorts; qname_and_index = _53_161.qname_and_index})))))
in (

let pop_stack = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _53_168 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _53_171 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let push = (fun env -> (

let _53_174 = (push_query_indices ())
in (push_stack env)))
in (

let pop = (fun env -> (

let _53_178 = (pop_query_indices ())
in (pop_stack env)))
in (

let mark = (fun env -> (

let _53_182 = (push_query_indices ())
in (push_stack env)))
in (

let commit_mark = (fun env -> (

let _53_186 = (commit_query_index_mark ())
in (

let _53_188 = (let _150_513 = (pop_stack env)
in (Prims.ignore _150_513))
in env)))
in (

let reset_mark = (fun env -> (

let _53_192 = (pop_query_indices ())
in (pop_stack env)))
in (

let incr_query_index = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(match ((FStar_All.pipe_right qix (FStar_List.tryFind (fun _53_205 -> (match (_53_205) with
| (m, _53_204) -> begin
(FStar_Ident.lid_equals l m)
end))))) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in (

let _53_208 = (add_query_index ((l), (next)))
in (

let _53_210 = env
in {solver = _53_210.solver; range = _53_210.range; curmodule = _53_210.curmodule; gamma = _53_210.gamma; gamma_cache = _53_210.gamma_cache; modules = _53_210.modules; expected_typ = _53_210.expected_typ; sigtab = _53_210.sigtab; is_pattern = _53_210.is_pattern; instantiate_imp = _53_210.instantiate_imp; effects = _53_210.effects; generalize = _53_210.generalize; letrecs = _53_210.letrecs; top_level = _53_210.top_level; check_uvars = _53_210.check_uvars; use_eq = _53_210.use_eq; is_iface = _53_210.is_iface; admit = _53_210.admit; lax = _53_210.lax; lax_universes = _53_210.lax_universes; type_of = _53_210.type_of; universe_of = _53_210.universe_of; use_bv_sorts = _53_210.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end
| Some (_53_213, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in (

let _53_218 = (add_query_index ((l), (next)))
in (

let _53_220 = env
in {solver = _53_220.solver; range = _53_220.range; curmodule = _53_220.curmodule; gamma = _53_220.gamma; gamma_cache = _53_220.gamma_cache; modules = _53_220.modules; expected_typ = _53_220.expected_typ; sigtab = _53_220.sigtab; is_pattern = _53_220.is_pattern; instantiate_imp = _53_220.instantiate_imp; effects = _53_220.effects; generalize = _53_220.generalize; letrecs = _53_220.letrecs; top_level = _53_220.top_level; check_uvars = _53_220.check_uvars; use_eq = _53_220.use_eq; is_iface = _53_220.is_iface; admit = _53_220.admit; lax = _53_220.lax; lax_universes = _53_220.lax_universes; type_of = _53_220.type_of; universe_of = _53_220.universe_of; use_bv_sorts = _53_220.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end)
end)))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop; es_incr_query_index = incr_query_index})))))))))))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _53_224 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _53_227 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _53_230 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _53_233 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _53_237 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let incr_query_index : env  ->  env = (fun env -> (stack_ops.es_incr_query_index env))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _53_244 = e
in {solver = _53_244.solver; range = r; curmodule = _53_244.curmodule; gamma = _53_244.gamma; gamma_cache = _53_244.gamma_cache; modules = _53_244.modules; expected_typ = _53_244.expected_typ; sigtab = _53_244.sigtab; is_pattern = _53_244.is_pattern; instantiate_imp = _53_244.instantiate_imp; effects = _53_244.effects; generalize = _53_244.generalize; letrecs = _53_244.letrecs; top_level = _53_244.top_level; check_uvars = _53_244.check_uvars; use_eq = _53_244.use_eq; is_iface = _53_244.is_iface; admit = _53_244.admit; lax = _53_244.lax; lax_universes = _53_244.lax_universes; type_of = _53_244.type_of; universe_of = _53_244.universe_of; use_bv_sorts = _53_244.use_bv_sorts; qname_and_index = _53_244.qname_and_index})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _53_251 = env
in {solver = _53_251.solver; range = _53_251.range; curmodule = lid; gamma = _53_251.gamma; gamma_cache = _53_251.gamma_cache; modules = _53_251.modules; expected_typ = _53_251.expected_typ; sigtab = _53_251.sigtab; is_pattern = _53_251.is_pattern; instantiate_imp = _53_251.instantiate_imp; effects = _53_251.effects; generalize = _53_251.generalize; letrecs = _53_251.letrecs; top_level = _53_251.top_level; check_uvars = _53_251.check_uvars; use_eq = _53_251.use_eq; is_iface = _53_251.is_iface; admit = _53_251.admit; lax = _53_251.lax; lax_universes = _53_251.lax_universes; type_of = _53_251.type_of; universe_of = _53_251.universe_of; use_bv_sorts = _53_251.use_bv_sorts; qname_and_index = _53_251.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _150_566 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _150_566)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _53_260 -> (match (()) with
| () -> begin
(let _150_569 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_150_569))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _53_272) -> begin
(

let _53_274 = ()
in (

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _150_576 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_150_576))))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _53_1 -> (match (_53_1) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _53_287 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let _53_294 = (inst_tscheme t)
in (match (_53_294) with
| (us, t) -> begin
(let _150_584 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (_150_584)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _53_300 -> (match (_53_300) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _53_303 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _150_597 = (let _150_596 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _150_595 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _150_594 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _150_593 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _150_596 _150_595 _150_594 _150_593)))))
in (FStar_All.failwith _150_597))
end else begin
()
end
in (let _150_598 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _150_598))))
end
| _53_306 -> begin
(let _150_600 = (let _150_599 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _150_599))
in (FStar_All.failwith _150_600))
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
| ([], _53_317) -> begin
Maybe
end
| (_53_320, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _53_331 -> begin
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

let _53_337 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _53_2 -> (match (_53_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _150_620 = (let _150_619 = (inst_tscheme t)
in FStar_Util.Inl (_150_619))
in Some (_150_620))
end else begin
None
end
end
| Binding_sig (_53_346, FStar_Syntax_Syntax.Sig_bundle (ses, _53_349, _53_351, _53_353)) -> begin
(FStar_Util.find_map ses (fun se -> if (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
(cache (FStar_Util.Inr (((se), (None)))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_53_366) -> begin
Some (t)
end
| _53_369 -> begin
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
| _53_376 -> begin
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
| FStar_Syntax_Syntax.Sig_bundle (ses, _53_386, _53_388, _53_390) -> begin
(add_sigelts env ses)
end
| _53_394 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let _53_397 = (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _53_401) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| _53_407 -> begin
()
end)))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _53_3 -> (match (_53_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _53_416 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_53_420, (lb)::[]), _53_425, _53_427, _53_429, _53_431) -> begin
(let _150_643 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_150_643))
end
| FStar_Syntax_Syntax.Sig_let ((_53_435, lbs), _53_439, _53_441, _53_443, _53_445) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_53_450) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _150_645 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_150_645))
end else begin
None
end
end)))
end
| _53_455 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _53_459) -> begin
(let _150_651 = (let _150_650 = (let _150_649 = (let _150_648 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _150_648))
in ((ne.FStar_Syntax_Syntax.univs), (_150_649)))
in (inst_tscheme _150_650))
in Some (_150_651))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _53_466, _53_468, _53_470, _53_472) -> begin
(let _150_655 = (let _150_654 = (let _150_653 = (let _150_652 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _150_652))
in ((us), (_150_653)))
in (inst_tscheme _150_654))
in Some (_150_655))
end
| _53_476 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun _53_4 -> (match (_53_4) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_53_483, uvs, t, _53_487, _53_489, _53_491, _53_493, _53_495), None) -> begin
(let _150_662 = (inst_tscheme ((uvs), (t)))
in Some (_150_662))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _53_506), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _150_663 = (inst_tscheme ((uvs), (t)))
in Some (_150_663))
end else begin
None
end
end else begin
(let _150_664 = (inst_tscheme ((uvs), (t)))
in Some (_150_664))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _53_517, _53_519, _53_521, _53_523), None) -> begin
(match (tps) with
| [] -> begin
(let _150_666 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _150_665 -> Some (_150_665)) _150_666))
end
| _53_531 -> begin
(let _150_671 = (let _150_670 = (let _150_669 = (let _150_668 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _150_668))
in ((uvs), (_150_669)))
in (inst_tscheme _150_670))
in (FStar_All.pipe_left (fun _150_667 -> Some (_150_667)) _150_671))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _53_537, _53_539, _53_541, _53_543), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _150_673 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _150_672 -> Some (_150_672)) _150_673))
end
| _53_552 -> begin
(let _150_678 = (let _150_677 = (let _150_676 = (let _150_675 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _150_675))
in ((uvs), (_150_676)))
in (inst_tscheme_with _150_677 us))
in (FStar_All.pipe_left (fun _150_674 -> Some (_150_674)) _150_678))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_53_556), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _53_561 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _150_679 = (lookup_qname env lid)
in (FStar_Util.bind_opt _150_679 mapper))) with
| Some (us, t) -> begin
Some (((us), ((

let _53_567 = t
in {FStar_Syntax_Syntax.n = _53_567.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_567.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _53_567.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end)))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_53_574) -> begin
true
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _150_691 = (let _150_690 = (let _150_689 = (variable_not_found bv)
in (let _150_688 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_150_689), (_150_688))))
in FStar_Syntax_Syntax.Error (_150_690))
in (Prims.raise _150_691))
end
| Some (t) -> begin
(let _150_692 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range _150_692 t))
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (match ((try_lookup_lid_aux env l)) with
| None -> begin
None
end
| Some (us, t) -> begin
(let _150_698 = (let _150_697 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (_150_697)))
in Some (_150_698))
end))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _150_705 = (let _150_704 = (let _150_703 = (name_not_found l)
in ((_150_703), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_150_704))
in (Prims.raise _150_705))
end
| Some (us, t) -> begin
((us), (t))
end))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _53_5 -> (match (_53_5) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _53_601 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_53_605, uvs, t, q, _53_610), None)) -> begin
(let _150_720 = (let _150_719 = (let _150_718 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (_150_718)))
in ((_150_719), (q)))
in Some (_150_720))
end
| _53_618 -> begin
None
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_53_622, uvs, t, _53_626, _53_628), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| _53_636 -> begin
(let _150_727 = (let _150_726 = (let _150_725 = (name_not_found lid)
in ((_150_725), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_150_726))
in (Prims.raise _150_727))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_53_640, uvs, t, _53_644, _53_646, _53_648, _53_650, _53_652), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| _53_660 -> begin
(let _150_734 = (let _150_733 = (let _150_732 = (name_not_found lid)
in ((_150_732), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_150_733))
in (Prims.raise _150_734))
end))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_53_664, _53_666, _53_668, _53_670, _53_672, dcs, _53_675, _53_677), _53_681)) -> begin
dcs
end
| _53_686 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_53_690, _53_692, _53_694, l, _53_697, _53_699, _53_701, _53_703), _53_707)) -> begin
l
end
| _53_712 -> begin
(let _150_744 = (let _150_743 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _150_743))
in (FStar_All.failwith _150_744))
end))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_53_725, lbs), _53_729, _53_731, quals, _53_734) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _150_757 = (let _150_756 = (let _150_755 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) _150_755))
in ((lb.FStar_Syntax_Syntax.lbunivs), (_150_756)))
in Some (_150_757))
end else begin
None
end)))
end
| _53_740 -> begin
None
end)
end
| _53_742 -> begin
None
end)))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_53_752, t) -> begin
(let _150_762 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (_150_762))
end)
end
| _53_757 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _150_769 = (let _150_768 = (let _150_767 = (name_not_found ftv)
in ((_150_767), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_150_768))
in (Prims.raise _150_769))
end
| Some (k) -> begin
k
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (match ((lookup_qname env lid0)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _53_772, _53_774), None)) -> begin
(

let lid = (let _150_776 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid _150_776))
in if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_6 -> (match (_53_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _53_785 -> begin
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
(let _150_780 = (let _150_779 = (FStar_Syntax_Print.lid_to_string lid)
in (let _150_778 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" _150_779 _150_778)))
in (FStar_All.failwith _150_780))
end
end
in (match (((binders), (univs))) with
| ([], _53_789) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_53_792, (_53_799)::(_53_796)::_53_794) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _150_783 = (let _150_782 = (FStar_Syntax_Print.lid_to_string lid)
in (let _150_781 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _150_782 _150_781)))
in (FStar_All.failwith _150_783))
end
| _53_803 -> begin
(

let _53_807 = (let _150_785 = (let _150_784 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_150_784)))
in (inst_tscheme_with _150_785 insts))
in (match (_53_807) with
| (_53_805, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (match ((let _150_786 = (FStar_Syntax_Subst.compress t)
in _150_786.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| _53_814 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))
end)
end
| _53_816 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)) with
| None -> begin
None
end
| Some (_53_824, c) -> begin
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

let _53_838 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in (FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l))))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l = (norm_eff_name env l)
in (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, _53_846), _53_850)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| _53_855 -> begin
[]
end)))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _53_860 -> (match (()) with
| () -> begin
(let _150_807 = (let _150_806 = (FStar_Util.string_of_int i)
in (let _150_805 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _150_806 _150_805)))
in (FStar_All.failwith _150_807))
end))
in (

let _53_864 = (lookup_datacon env lid)
in (match (_53_864) with
| (_53_862, t) -> begin
(match ((let _150_808 = (FStar_Syntax_Subst.compress t)
in _150_808.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _53_867) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _150_809 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _150_809 Prims.fst)))
end
end
| _53_872 -> begin
(fail ())
end)
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_53_876, _53_878, _53_880, quals, _53_883), _53_887)) -> begin
(FStar_Util.for_some (fun _53_7 -> (match (_53_7) with
| FStar_Syntax_Syntax.Projector (_53_893) -> begin
true
end
| _53_896 -> begin
false
end)) quals)
end
| _53_898 -> begin
false
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_53_902, _53_904, _53_906, _53_908, _53_910, _53_912, _53_914, _53_916), _53_920)) -> begin
true
end
| _53_925 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_53_929, _53_931, _53_933, _53_935, _53_937, _53_939, tags, _53_942), _53_946)) -> begin
(FStar_Util.for_some (fun _53_8 -> (match (_53_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _53_958 -> begin
false
end)) tags)
end
| _53_960 -> begin
false
end))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (match ((let _150_828 = (FStar_Syntax_Util.un_uinst head)
in _150_828.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _53_967 -> begin
false
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _53_9 -> (match (_53_9) with
| FStar_Util.Inl (_53_972) -> begin
Some (false)
end
| FStar_Util.Inr (se, _53_976) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_53_980, _53_982, _53_984, qs, _53_987) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_53_991) -> begin
Some (true)
end
| _53_994 -> begin
Some (false)
end)
end))
in (match ((let _150_835 = (lookup_qname env lid)
in (FStar_Util.bind_opt _150_835 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _150_847 = (let _150_846 = (let _150_845 = (name_not_found l)
in ((_150_845), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_150_846))
in (Prims.raise _150_847))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _53_1026 -> (match (_53_1026) with
| (m1, m2, _53_1021, _53_1023, _53_1025) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _150_923 = (let _150_922 = (let _150_921 = (let _150_920 = (FStar_Syntax_Print.lid_to_string l1)
in (let _150_919 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _150_920 _150_919)))
in ((_150_921), (env.range)))
in FStar_Syntax_Syntax.Error (_150_922))
in (Prims.raise _150_923))
end
| Some (_53_1029, _53_1031, m3, j1, j2) -> begin
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
(let _150_938 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _150_938))
end
| Some (md) -> begin
(

let _53_1052 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_53_1052) with
| (_53_1050, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _53_1061))::((wp, _53_1057))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _53_1069 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _53_1076) -> begin
(

let effects = (

let _53_1079 = env.effects
in {decls = (ne)::env.effects.decls; order = _53_1079.order; joins = _53_1079.joins})
in (

let _53_1082 = env
in {solver = _53_1082.solver; range = _53_1082.range; curmodule = _53_1082.curmodule; gamma = _53_1082.gamma; gamma_cache = _53_1082.gamma_cache; modules = _53_1082.modules; expected_typ = _53_1082.expected_typ; sigtab = _53_1082.sigtab; is_pattern = _53_1082.is_pattern; instantiate_imp = _53_1082.instantiate_imp; effects = effects; generalize = _53_1082.generalize; letrecs = _53_1082.letrecs; top_level = _53_1082.top_level; check_uvars = _53_1082.check_uvars; use_eq = _53_1082.use_eq; is_iface = _53_1082.is_iface; admit = _53_1082.admit; lax = _53_1082.lax; lax_universes = _53_1082.lax_universes; type_of = _53_1082.type_of; universe_of = _53_1082.universe_of; use_bv_sorts = _53_1082.use_bv_sorts; qname_and_index = _53_1082.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _53_1086) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _150_953 = (e1.mlift r wp1)
in (e2.mlift r _150_953)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _53_1101 = (inst_tscheme lift_t)
in (match (_53_1101) with
| (_53_1099, lift_t) -> begin
(let _150_965 = (let _150_964 = (let _150_963 = (let _150_962 = (FStar_Syntax_Syntax.as_arg r)
in (let _150_961 = (let _150_960 = (FStar_Syntax_Syntax.as_arg wp1)
in (_150_960)::[])
in (_150_962)::_150_961))
in ((lift_t), (_150_963)))
in FStar_Syntax_Syntax.Tm_app (_150_964))
in (FStar_Syntax_Syntax.mk _150_965 None wp1.FStar_Syntax_Syntax.pos))
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

let arg = (let _150_982 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _150_982 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _150_983 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _150_983 FStar_Syntax_Syntax.Delta_constant None))
in (let _150_984 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _150_984)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _53_1122 -> (match (_53_1122) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _150_990 -> Some (_150_990)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _150_998 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _150_997 = (find_edge order ((i), (k)))
in (let _150_996 = (find_edge order ((k), (j)))
in ((_150_997), (_150_996))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _53_1134 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _150_998))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let _53_1140 = (FStar_All.pipe_right order (FStar_List.iter (fun edge -> if ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (let _150_1002 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right _150_1002 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))) then begin
(let _150_1006 = (let _150_1005 = (let _150_1004 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (let _150_1003 = (get_range env)
in ((_150_1004), (_150_1003))))
in FStar_Syntax_Syntax.Error (_150_1005))
in (Prims.raise _150_1006))
end else begin
()
end)))
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _150_1096 = (find_edge order ((i), (k)))
in (let _150_1095 = (find_edge order ((j), (k)))
in ((_150_1096), (_150_1095))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _53_1154, _53_1156) -> begin
if ((let _150_1097 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _150_1097)) && (not ((let _150_1098 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _150_1098))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _53_1160 -> begin
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

let _53_1169 = env.effects
in {decls = _53_1169.decls; order = order; joins = joins})
in (

let _53_1172 = env
in {solver = _53_1172.solver; range = _53_1172.range; curmodule = _53_1172.curmodule; gamma = _53_1172.gamma; gamma_cache = _53_1172.gamma_cache; modules = _53_1172.modules; expected_typ = _53_1172.expected_typ; sigtab = _53_1172.sigtab; is_pattern = _53_1172.is_pattern; instantiate_imp = _53_1172.instantiate_imp; effects = effects; generalize = _53_1172.generalize; letrecs = _53_1172.letrecs; top_level = _53_1172.top_level; check_uvars = _53_1172.check_uvars; use_eq = _53_1172.use_eq; is_iface = _53_1172.is_iface; admit = _53_1172.admit; lax = _53_1172.lax; lax_universes = _53_1172.lax_universes; type_of = _53_1172.type_of; universe_of = _53_1172.universe_of; use_bv_sorts = _53_1172.use_bv_sorts; qname_and_index = _53_1172.qname_and_index})))))))))))))))
end
| _53_1175 -> begin
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
(let _150_1147 = (push x rest)
in (local)::_150_1147)
end))
in (

let _53_1197 = env
in (let _150_1148 = (push s env.gamma)
in {solver = _53_1197.solver; range = _53_1197.range; curmodule = _53_1197.curmodule; gamma = _150_1148; gamma_cache = _53_1197.gamma_cache; modules = _53_1197.modules; expected_typ = _53_1197.expected_typ; sigtab = _53_1197.sigtab; is_pattern = _53_1197.is_pattern; instantiate_imp = _53_1197.instantiate_imp; effects = _53_1197.effects; generalize = _53_1197.generalize; letrecs = _53_1197.letrecs; top_level = _53_1197.top_level; check_uvars = _53_1197.check_uvars; use_eq = _53_1197.use_eq; is_iface = _53_1197.is_iface; admit = _53_1197.admit; lax = _53_1197.lax; lax_universes = _53_1197.lax_universes; type_of = _53_1197.type_of; universe_of = _53_1197.universe_of; use_bv_sorts = _53_1197.use_bv_sorts; qname_and_index = _53_1197.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _53_1208 = env
in {solver = _53_1208.solver; range = _53_1208.range; curmodule = _53_1208.curmodule; gamma = (b)::env.gamma; gamma_cache = _53_1208.gamma_cache; modules = _53_1208.modules; expected_typ = _53_1208.expected_typ; sigtab = _53_1208.sigtab; is_pattern = _53_1208.is_pattern; instantiate_imp = _53_1208.instantiate_imp; effects = _53_1208.effects; generalize = _53_1208.generalize; letrecs = _53_1208.letrecs; top_level = _53_1208.top_level; check_uvars = _53_1208.check_uvars; use_eq = _53_1208.use_eq; is_iface = _53_1208.is_iface; admit = _53_1208.admit; lax = _53_1208.lax; lax_universes = _53_1208.lax_universes; type_of = _53_1208.type_of; universe_of = _53_1208.universe_of; use_bv_sorts = _53_1208.use_bv_sorts; qname_and_index = _53_1208.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _53_1218 -> (match (_53_1218) with
| (x, _53_1217) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _53_1223 = ()
in (

let x = (

let _53_1225 = x
in {FStar_Syntax_Syntax.ppname = _53_1225.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1225.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _53_1235 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _53_1237 = env
in {solver = _53_1237.solver; range = _53_1237.range; curmodule = _53_1237.curmodule; gamma = []; gamma_cache = _53_1237.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _53_1237.sigtab; is_pattern = _53_1237.is_pattern; instantiate_imp = _53_1237.instantiate_imp; effects = _53_1237.effects; generalize = _53_1237.generalize; letrecs = _53_1237.letrecs; top_level = _53_1237.top_level; check_uvars = _53_1237.check_uvars; use_eq = _53_1237.use_eq; is_iface = _53_1237.is_iface; admit = _53_1237.admit; lax = _53_1237.lax; lax_universes = _53_1237.lax_universes; type_of = _53_1237.type_of; universe_of = _53_1237.universe_of; use_bv_sorts = _53_1237.use_bv_sorts; qname_and_index = _53_1237.qname_and_index})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _53_1245 = env
in {solver = _53_1245.solver; range = _53_1245.range; curmodule = _53_1245.curmodule; gamma = _53_1245.gamma; gamma_cache = _53_1245.gamma_cache; modules = _53_1245.modules; expected_typ = Some (t); sigtab = _53_1245.sigtab; is_pattern = _53_1245.is_pattern; instantiate_imp = _53_1245.instantiate_imp; effects = _53_1245.effects; generalize = _53_1245.generalize; letrecs = _53_1245.letrecs; top_level = _53_1245.top_level; check_uvars = _53_1245.check_uvars; use_eq = false; is_iface = _53_1245.is_iface; admit = _53_1245.admit; lax = _53_1245.lax; lax_universes = _53_1245.lax_universes; type_of = _53_1245.type_of; universe_of = _53_1245.universe_of; use_bv_sorts = _53_1245.use_bv_sorts; qname_and_index = _53_1245.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _150_1201 = (expected_typ env)
in (((

let _53_1252 = env
in {solver = _53_1252.solver; range = _53_1252.range; curmodule = _53_1252.curmodule; gamma = _53_1252.gamma; gamma_cache = _53_1252.gamma_cache; modules = _53_1252.modules; expected_typ = None; sigtab = _53_1252.sigtab; is_pattern = _53_1252.is_pattern; instantiate_imp = _53_1252.instantiate_imp; effects = _53_1252.effects; generalize = _53_1252.generalize; letrecs = _53_1252.letrecs; top_level = _53_1252.top_level; check_uvars = _53_1252.check_uvars; use_eq = false; is_iface = _53_1252.is_iface; admit = _53_1252.admit; lax = _53_1252.lax; lax_universes = _53_1252.lax_universes; type_of = _53_1252.type_of; universe_of = _53_1252.universe_of; use_bv_sorts = _53_1252.use_bv_sorts; qname_and_index = _53_1252.qname_and_index})), (_150_1201))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _150_1207 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _53_10 -> (match (_53_10) with
| Binding_sig (_53_1259, se) -> begin
(se)::[]
end
| _53_1264 -> begin
[]
end))))
in (FStar_All.pipe_right _150_1207 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _53_1266 = (add_sigelts env sigs)
in (

let _53_1268 = env
in {solver = _53_1268.solver; range = _53_1268.range; curmodule = empty_lid; gamma = []; gamma_cache = _53_1268.gamma_cache; modules = (m)::env.modules; expected_typ = _53_1268.expected_typ; sigtab = _53_1268.sigtab; is_pattern = _53_1268.is_pattern; instantiate_imp = _53_1268.instantiate_imp; effects = _53_1268.effects; generalize = _53_1268.generalize; letrecs = _53_1268.letrecs; top_level = _53_1268.top_level; check_uvars = _53_1268.check_uvars; use_eq = _53_1268.use_eq; is_iface = _53_1268.is_iface; admit = _53_1268.admit; lax = _53_1268.lax; lax_universes = _53_1268.lax_universes; type_of = _53_1268.type_of; universe_of = _53_1268.universe_of; use_bv_sorts = _53_1268.use_bv_sorts; qname_and_index = _53_1268.qname_and_index})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_53_1281))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _150_1219 = (let _150_1218 = (FStar_Syntax_Free.uvars t)
in (ext out _150_1218))
in (aux _150_1219 tl))
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
(let _150_1231 = (let _150_1230 = (FStar_Syntax_Free.univs t)
in (ext out _150_1230))
in (aux _150_1231 tl))
end
| (Binding_sig (_53_1351))::_53_1349 -> begin
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
| (Binding_sig_inst (_53_1365))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(let _150_1242 = (FStar_Util.set_add uname out)
in (aux _150_1242 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _150_1244 = (let _150_1243 = (FStar_Syntax_Free.univnames t)
in (ext out _150_1243))
in (aux _150_1244 tl))
end
| (Binding_sig (_53_1392))::_53_1390 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _53_11 -> (match (_53_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _150_1251 = (let _150_1250 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _150_1250 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _150_1251 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _53_12 -> (match (_53_12) with
| Binding_sig (lids, _53_1424) -> begin
(FStar_List.append lids keys)
end
| _53_1428 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _53_1430 v keys -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)) keys)))


let dummy_solver : solver_t = {init = (fun _53_1434 -> ()); push = (fun _53_1436 -> ()); pop = (fun _53_1438 -> ()); mark = (fun _53_1440 -> ()); reset_mark = (fun _53_1442 -> ()); commit_mark = (fun _53_1444 -> ()); encode_modul = (fun _53_1446 _53_1448 -> ()); encode_sig = (fun _53_1450 _53_1452 -> ()); solve = (fun _53_1454 _53_1456 _53_1458 -> ()); is_trivial = (fun _53_1460 _53_1462 -> false); finish = (fun _53_1464 -> ()); refresh = (fun _53_1465 -> ())}




