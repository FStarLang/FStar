
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
| _52_107 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun _52_108 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _52_109 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _149_422 = (new_gamma_cache ())
in (let _149_421 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _149_422; modules = []; expected_typ = None; sigtab = _149_421; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun _52_125 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| [] -> begin
(FStar_All.failwith "Empty query indices!")
end
| _52_128 -> begin
(let _149_487 = (let _149_486 = (let _149_484 = (FStar_ST.read query_indices)
in (FStar_List.hd _149_484))
in (let _149_485 = (FStar_ST.read query_indices)
in (_149_486)::_149_485))
in (FStar_ST.op_Colon_Equals query_indices _149_487))
end)
end))
in (

let pop_query_indices = (fun _52_130 -> (match (()) with
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

let add_query_index = (fun _52_138 -> (match (_52_138) with
| (l, n) -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n)))::hd)::tl))
end
| _52_143 -> begin
(FStar_All.failwith "Empty query indices")
end)
end))
in (

let peek_query_indices = (fun _52_145 -> (match (()) with
| () -> begin
(let _149_494 = (FStar_ST.read query_indices)
in (FStar_List.hd _149_494))
end))
in (

let commit_query_index_mark = (fun _52_147 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::(_52_150)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices ((hd)::tl))
end
| _52_155 -> begin
(FStar_All.failwith "Unmarked query index stack")
end)
end))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> (

let _52_159 = (let _149_500 = (let _149_499 = (FStar_ST.read stack)
in (env)::_149_499)
in (FStar_ST.op_Colon_Equals stack _149_500))
in (

let _52_161 = env
in (let _149_502 = (FStar_Util.smap_copy (gamma_cache env))
in (let _149_501 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_161.solver; range = _52_161.range; curmodule = _52_161.curmodule; gamma = _52_161.gamma; gamma_cache = _149_502; modules = _52_161.modules; expected_typ = _52_161.expected_typ; sigtab = _149_501; is_pattern = _52_161.is_pattern; instantiate_imp = _52_161.instantiate_imp; effects = _52_161.effects; generalize = _52_161.generalize; letrecs = _52_161.letrecs; top_level = _52_161.top_level; check_uvars = _52_161.check_uvars; use_eq = _52_161.use_eq; is_iface = _52_161.is_iface; admit = _52_161.admit; lax = _52_161.lax; lax_universes = _52_161.lax_universes; type_of = _52_161.type_of; universe_of = _52_161.universe_of; use_bv_sorts = _52_161.use_bv_sorts; qname_and_index = _52_161.qname_and_index})))))
in (

let pop_stack = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_168 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_171 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let push = (fun env -> (

let _52_174 = (push_query_indices ())
in (push_stack env)))
in (

let pop = (fun env -> (

let _52_178 = (pop_query_indices ())
in (pop_stack env)))
in (

let mark = (fun env -> (

let _52_182 = (push_query_indices ())
in (push_stack env)))
in (

let commit_mark = (fun env -> (

let _52_186 = (commit_query_index_mark ())
in (

let _52_188 = (let _149_513 = (pop_stack env)
in (Prims.ignore _149_513))
in env)))
in (

let reset_mark = (fun env -> (

let _52_192 = (pop_query_indices ())
in (pop_stack env)))
in (

let incr_query_index = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(match ((FStar_All.pipe_right qix (FStar_List.tryFind (fun _52_205 -> (match (_52_205) with
| (m, _52_204) -> begin
(FStar_Ident.lid_equals l m)
end))))) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in (

let _52_208 = (add_query_index ((l), (next)))
in (

let _52_210 = env
in {solver = _52_210.solver; range = _52_210.range; curmodule = _52_210.curmodule; gamma = _52_210.gamma; gamma_cache = _52_210.gamma_cache; modules = _52_210.modules; expected_typ = _52_210.expected_typ; sigtab = _52_210.sigtab; is_pattern = _52_210.is_pattern; instantiate_imp = _52_210.instantiate_imp; effects = _52_210.effects; generalize = _52_210.generalize; letrecs = _52_210.letrecs; top_level = _52_210.top_level; check_uvars = _52_210.check_uvars; use_eq = _52_210.use_eq; is_iface = _52_210.is_iface; admit = _52_210.admit; lax = _52_210.lax; lax_universes = _52_210.lax_universes; type_of = _52_210.type_of; universe_of = _52_210.universe_of; use_bv_sorts = _52_210.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end
| Some (_52_213, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in (

let _52_218 = (add_query_index ((l), (next)))
in (

let _52_220 = env
in {solver = _52_220.solver; range = _52_220.range; curmodule = _52_220.curmodule; gamma = _52_220.gamma; gamma_cache = _52_220.gamma_cache; modules = _52_220.modules; expected_typ = _52_220.expected_typ; sigtab = _52_220.sigtab; is_pattern = _52_220.is_pattern; instantiate_imp = _52_220.instantiate_imp; effects = _52_220.effects; generalize = _52_220.generalize; letrecs = _52_220.letrecs; top_level = _52_220.top_level; check_uvars = _52_220.check_uvars; use_eq = _52_220.use_eq; is_iface = _52_220.is_iface; admit = _52_220.admit; lax = _52_220.lax; lax_universes = _52_220.lax_universes; type_of = _52_220.type_of; universe_of = _52_220.universe_of; use_bv_sorts = _52_220.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end)
end)))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop; es_incr_query_index = incr_query_index})))))))))))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_224 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_227 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_230 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_233 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_237 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let incr_query_index : env  ->  env = (fun env -> (stack_ops.es_incr_query_index env))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_244 = e
in {solver = _52_244.solver; range = r; curmodule = _52_244.curmodule; gamma = _52_244.gamma; gamma_cache = _52_244.gamma_cache; modules = _52_244.modules; expected_typ = _52_244.expected_typ; sigtab = _52_244.sigtab; is_pattern = _52_244.is_pattern; instantiate_imp = _52_244.instantiate_imp; effects = _52_244.effects; generalize = _52_244.generalize; letrecs = _52_244.letrecs; top_level = _52_244.top_level; check_uvars = _52_244.check_uvars; use_eq = _52_244.use_eq; is_iface = _52_244.is_iface; admit = _52_244.admit; lax = _52_244.lax; lax_universes = _52_244.lax_universes; type_of = _52_244.type_of; universe_of = _52_244.universe_of; use_bv_sorts = _52_244.use_bv_sorts; qname_and_index = _52_244.qname_and_index})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_251 = env
in {solver = _52_251.solver; range = _52_251.range; curmodule = lid; gamma = _52_251.gamma; gamma_cache = _52_251.gamma_cache; modules = _52_251.modules; expected_typ = _52_251.expected_typ; sigtab = _52_251.sigtab; is_pattern = _52_251.is_pattern; instantiate_imp = _52_251.instantiate_imp; effects = _52_251.effects; generalize = _52_251.generalize; letrecs = _52_251.letrecs; top_level = _52_251.top_level; check_uvars = _52_251.check_uvars; use_eq = _52_251.use_eq; is_iface = _52_251.is_iface; admit = _52_251.admit; lax = _52_251.lax; lax_universes = _52_251.lax_universes; type_of = _52_251.type_of; universe_of = _52_251.universe_of; use_bv_sorts = _52_251.use_bv_sorts; qname_and_index = _52_251.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _149_566 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _149_566)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _52_260 -> (match (()) with
| () -> begin
(let _149_569 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_149_569))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _52_272) -> begin
(

let _52_274 = ()
in (

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _149_576 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_149_576))))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_287 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_295 -> (match (_52_295) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_298 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _149_592 = (let _149_591 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _149_590 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _149_589 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _149_588 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _149_591 _149_590 _149_589 _149_588)))))
in (FStar_All.failwith _149_592))
end else begin
()
end
in (let _149_593 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _149_593))))
end
| _52_301 -> begin
(let _149_595 = (let _149_594 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _149_594))
in (FStar_All.failwith _149_595))
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
| ([], _52_312) -> begin
Maybe
end
| (_52_315, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_326 -> begin
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

let _52_332 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _149_615 = (let _149_614 = (inst_tscheme t)
in FStar_Util.Inl (_149_614))
in Some (_149_615))
end else begin
None
end
end
| Binding_sig (_52_341, FStar_Syntax_Syntax.Sig_bundle (ses, _52_344, _52_346, _52_348)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _149_617 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _149_617 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr (((se), (None)))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_361) -> begin
Some (t)
end
| _52_364 -> begin
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
| _52_371 -> begin
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


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_52_381) -> begin
true
end))


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


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_4 -> (match (_52_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_424 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_428, (lb)::[]), _52_433, _52_435, _52_437) -> begin
(let _149_651 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_149_651))
end
| FStar_Syntax_Syntax.Sig_let ((_52_441, lbs), _52_445, _52_447, _52_449) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_454) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _149_653 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_149_653))
end else begin
None
end
end)))
end
| _52_459 -> begin
None
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _149_661 = (let _149_660 = (let _149_659 = (variable_not_found bv)
in (let _149_658 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_149_659), (_149_658))))
in FStar_Syntax_Syntax.Error (_149_660))
in (Prims.raise _149_661))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_468) -> begin
(let _149_667 = (let _149_666 = (let _149_665 = (let _149_664 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _149_664))
in ((ne.FStar_Syntax_Syntax.univs), (_149_665)))
in (inst_tscheme _149_666))
in Some (_149_667))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_475, _52_477, _52_479) -> begin
(let _149_671 = (let _149_670 = (let _149_669 = (let _149_668 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _149_668))
in ((us), (_149_669)))
in (inst_tscheme _149_670))
in Some (_149_671))
end
| _52_483 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_493, t) -> begin
Some (t)
end)
end
| _52_498 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (

let mapper = (fun _52_5 -> (match (_52_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_505, uvs, t, _52_509, _52_511, _52_513, _52_515, _52_517), None) -> begin
(let _149_682 = (inst_tscheme ((uvs), (t)))
in Some (_149_682))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_528), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _149_683 = (inst_tscheme ((uvs), (t)))
in Some (_149_683))
end else begin
None
end
end else begin
(let _149_684 = (inst_tscheme ((uvs), (t)))
in Some (_149_684))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_539, _52_541, _52_543, _52_545), None) -> begin
(match (tps) with
| [] -> begin
(let _149_686 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _149_685 -> Some (_149_685)) _149_686))
end
| _52_553 -> begin
(let _149_691 = (let _149_690 = (let _149_689 = (let _149_688 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _149_688))
in ((uvs), (_149_689)))
in (inst_tscheme _149_690))
in (FStar_All.pipe_left (fun _149_687 -> Some (_149_687)) _149_691))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_559, _52_561, _52_563, _52_565), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _149_693 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _149_692 -> Some (_149_692)) _149_693))
end
| _52_574 -> begin
(let _149_698 = (let _149_697 = (let _149_696 = (let _149_695 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _149_695))
in ((uvs), (_149_696)))
in (inst_tscheme_with _149_697 us))
in (FStar_All.pipe_left (fun _149_694 -> Some (_149_694)) _149_698))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_578), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_583 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _149_699 = (lookup_qname env lid)
in (FStar_Util.bind_opt _149_699 mapper))) with
| Some (us, t) -> begin
Some (((us), ((

let _52_589 = t
in {FStar_Syntax_Syntax.n = _52_589.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_589.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_589.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_6 -> (match (_52_6) with
| FStar_Util.Inl (_52_596) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_600) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_604, _52_606, _52_608, qs, _52_611) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_615) -> begin
Some (true)
end
| _52_618 -> begin
Some (false)
end)
end))
in (match ((let _149_706 = (lookup_qname env lid)
in (FStar_Util.bind_opt _149_706 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _149_713 = (let _149_712 = (let _149_711 = (name_not_found l)
in ((_149_711), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_149_712))
in (Prims.raise _149_713))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_631, uvs, t, _52_635, _52_637), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_645 -> begin
(let _149_720 = (let _149_719 = (let _149_718 = (name_not_found lid)
in ((_149_718), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_149_719))
in (Prims.raise _149_720))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_649, uvs, t, _52_653, _52_655, _52_657, _52_659, _52_661), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_669 -> begin
(let _149_727 = (let _149_726 = (let _149_725 = (name_not_found lid)
in ((_149_725), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_149_726))
in (Prims.raise _149_727))
end))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_682, lbs), _52_686, _52_688, quals) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _149_739 = (let _149_738 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in ((lb.FStar_Syntax_Syntax.lbunivs), (_149_738)))
in Some (_149_739))
end else begin
None
end)))
end
| _52_695 -> begin
None
end)
end
| _52_697 -> begin
None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _149_746 = (let _149_745 = (let _149_744 = (name_not_found ftv)
in ((_149_744), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_149_745))
in (Prims.raise _149_746))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_707 -> (match (()) with
| () -> begin
(let _149_757 = (let _149_756 = (FStar_Util.string_of_int i)
in (let _149_755 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _149_756 _149_755)))
in (FStar_All.failwith _149_757))
end))
in (

let _52_711 = (lookup_datacon env lid)
in (match (_52_711) with
| (_52_709, t) -> begin
(match ((let _149_758 = (FStar_Syntax_Subst.compress t)
in _149_758.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_714) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _149_759 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _149_759 Prims.fst)))
end
end
| _52_719 -> begin
(fail ())
end)
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_723, uvs, t, q, _52_728), None)) -> begin
Some (((((uvs), (t))), (q)))
end
| _52_736 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_746), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_756 -> begin
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
(let _149_773 = (let _149_772 = (FStar_Syntax_Print.lid_to_string lid)
in (let _149_771 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" _149_772 _149_771)))
in (FStar_All.failwith _149_773))
end
end
in (match (((binders), (univs))) with
| ([], _52_760) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_763, (_52_770)::(_52_767)::_52_765) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _149_776 = (let _149_775 = (FStar_Syntax_Print.lid_to_string lid)
in (let _149_774 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _149_775 _149_774)))
in (FStar_All.failwith _149_776))
end
| _52_774 -> begin
(

let _52_778 = (let _149_778 = (let _149_777 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_149_777)))
in (inst_tscheme_with _149_778 insts))
in (match (_52_778) with
| (_52_776, t) -> begin
(match ((let _149_779 = (FStar_Syntax_Subst.compress t)
in _149_779.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| _52_784 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_786 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)) with
| None -> begin
None
end
| Some (_52_794, c) -> begin
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

let _52_808 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l = (norm_eff_name env l)
in (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, _52_816), _52_820)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| _52_825 -> begin
[]
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_829, _52_831, _52_833, _52_835, _52_837, dcs, _52_840, _52_842), _52_846)) -> begin
dcs
end
| _52_851 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_855, _52_857, _52_859, l, _52_862, _52_864, _52_866, _52_868), _52_872)) -> begin
l
end
| _52_877 -> begin
(let _149_799 = (let _149_798 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _149_798))
in (FStar_All.failwith _149_799))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_881, _52_883, _52_885, _52_887, _52_889, _52_891, _52_893, _52_895), _52_899)) -> begin
true
end
| _52_904 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_908, _52_910, _52_912, _52_914, _52_916, _52_918, tags, _52_921), _52_925)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_937 -> begin
false
end)) tags)
end
| _52_939 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_943, _52_945, _52_947, quals, _52_950), _52_954)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_960) -> begin
true
end
| _52_963 -> begin
false
end)) quals)
end
| _52_965 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _149_818 = (FStar_Syntax_Util.un_uinst head)
in _149_818.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_971 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _149_830 = (let _149_829 = (let _149_828 = (name_not_found l)
in ((_149_828), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_149_829))
in (Prims.raise _149_830))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_999 -> (match (_52_999) with
| (m1, m2, _52_994, _52_996, _52_998) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _149_906 = (let _149_905 = (let _149_904 = (let _149_903 = (FStar_Syntax_Print.lid_to_string l1)
in (let _149_902 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _149_903 _149_902)))
in ((_149_904), (env.range)))
in FStar_Syntax_Syntax.Error (_149_905))
in (Prims.raise _149_906))
end
| Some (_52_1002, _52_1004, m3, j1, j2) -> begin
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
(let _149_921 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _149_921))
end
| Some (md) -> begin
(

let _52_1025 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_52_1025) with
| (_52_1023, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_1034))::((wp, _52_1030))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _52_1042 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_1049) -> begin
(

let effects = (

let _52_1052 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1052.order; joins = _52_1052.joins})
in (

let _52_1055 = env
in {solver = _52_1055.solver; range = _52_1055.range; curmodule = _52_1055.curmodule; gamma = _52_1055.gamma; gamma_cache = _52_1055.gamma_cache; modules = _52_1055.modules; expected_typ = _52_1055.expected_typ; sigtab = _52_1055.sigtab; is_pattern = _52_1055.is_pattern; instantiate_imp = _52_1055.instantiate_imp; effects = effects; generalize = _52_1055.generalize; letrecs = _52_1055.letrecs; top_level = _52_1055.top_level; check_uvars = _52_1055.check_uvars; use_eq = _52_1055.use_eq; is_iface = _52_1055.is_iface; admit = _52_1055.admit; lax = _52_1055.lax; lax_universes = _52_1055.lax_universes; type_of = _52_1055.type_of; universe_of = _52_1055.universe_of; use_bv_sorts = _52_1055.use_bv_sorts; qname_and_index = _52_1055.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1059) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _149_936 = (e1.mlift r wp1)
in (e2.mlift r _149_936)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1074 = (inst_tscheme lift_t)
in (match (_52_1074) with
| (_52_1072, lift_t) -> begin
(let _149_948 = (let _149_947 = (let _149_946 = (let _149_945 = (FStar_Syntax_Syntax.as_arg r)
in (let _149_944 = (let _149_943 = (FStar_Syntax_Syntax.as_arg wp1)
in (_149_943)::[])
in (_149_945)::_149_944))
in ((lift_t), (_149_946)))
in FStar_Syntax_Syntax.Tm_app (_149_947))
in (FStar_Syntax_Syntax.mk _149_948 None wp1.FStar_Syntax_Syntax.pos))
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

let arg = (let _149_965 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _149_965 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _149_966 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _149_966 FStar_Syntax_Syntax.Delta_constant None))
in (let _149_967 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _149_967)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1095 -> (match (_52_1095) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _149_973 -> Some (_149_973)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _149_981 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _149_980 = (find_edge order ((i), (k)))
in (let _149_979 = (find_edge order ((k), (j)))
in ((_149_980), (_149_979))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1107 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _149_981))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let _52_1113 = (FStar_All.pipe_right order (FStar_List.iter (fun edge -> if ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (let _149_985 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right _149_985 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))) then begin
(let _149_989 = (let _149_988 = (let _149_987 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (let _149_986 = (get_range env)
in ((_149_987), (_149_986))))
in FStar_Syntax_Syntax.Error (_149_988))
in (Prims.raise _149_989))
end else begin
()
end)))
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _149_1079 = (find_edge order ((i), (k)))
in (let _149_1078 = (find_edge order ((j), (k)))
in ((_149_1079), (_149_1078))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _52_1127, _52_1129) -> begin
if ((let _149_1080 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _149_1080)) && (not ((let _149_1081 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _149_1081))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _52_1133 -> begin
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

let _52_1142 = env.effects
in {decls = _52_1142.decls; order = order; joins = joins})
in (

let _52_1145 = env
in {solver = _52_1145.solver; range = _52_1145.range; curmodule = _52_1145.curmodule; gamma = _52_1145.gamma; gamma_cache = _52_1145.gamma_cache; modules = _52_1145.modules; expected_typ = _52_1145.expected_typ; sigtab = _52_1145.sigtab; is_pattern = _52_1145.is_pattern; instantiate_imp = _52_1145.instantiate_imp; effects = effects; generalize = _52_1145.generalize; letrecs = _52_1145.letrecs; top_level = _52_1145.top_level; check_uvars = _52_1145.check_uvars; use_eq = _52_1145.use_eq; is_iface = _52_1145.is_iface; admit = _52_1145.admit; lax = _52_1145.lax; lax_universes = _52_1145.lax_universes; type_of = _52_1145.type_of; universe_of = _52_1145.universe_of; use_bv_sorts = _52_1145.use_bv_sorts; qname_and_index = _52_1145.qname_and_index})))))))))))))))
end
| _52_1148 -> begin
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
(let _149_1130 = (push x rest)
in (local)::_149_1130)
end))
in (

let _52_1170 = env
in (let _149_1131 = (push s env.gamma)
in {solver = _52_1170.solver; range = _52_1170.range; curmodule = _52_1170.curmodule; gamma = _149_1131; gamma_cache = _52_1170.gamma_cache; modules = _52_1170.modules; expected_typ = _52_1170.expected_typ; sigtab = _52_1170.sigtab; is_pattern = _52_1170.is_pattern; instantiate_imp = _52_1170.instantiate_imp; effects = _52_1170.effects; generalize = _52_1170.generalize; letrecs = _52_1170.letrecs; top_level = _52_1170.top_level; check_uvars = _52_1170.check_uvars; use_eq = _52_1170.use_eq; is_iface = _52_1170.is_iface; admit = _52_1170.admit; lax = _52_1170.lax; lax_universes = _52_1170.lax_universes; type_of = _52_1170.type_of; universe_of = _52_1170.universe_of; use_bv_sorts = _52_1170.use_bv_sorts; qname_and_index = _52_1170.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (let _149_1138 = (let _149_1137 = (let _149_1136 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_149_1136), (s)))
in Binding_sig (_149_1137))
in (push_in_gamma env _149_1138))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (let _149_1147 = (let _149_1146 = (let _149_1145 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_149_1145), (s), (us)))
in Binding_sig_inst (_149_1146))
in (push_in_gamma env _149_1147))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1181 = env
in {solver = _52_1181.solver; range = _52_1181.range; curmodule = _52_1181.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1181.gamma_cache; modules = _52_1181.modules; expected_typ = _52_1181.expected_typ; sigtab = _52_1181.sigtab; is_pattern = _52_1181.is_pattern; instantiate_imp = _52_1181.instantiate_imp; effects = _52_1181.effects; generalize = _52_1181.generalize; letrecs = _52_1181.letrecs; top_level = _52_1181.top_level; check_uvars = _52_1181.check_uvars; use_eq = _52_1181.use_eq; is_iface = _52_1181.is_iface; admit = _52_1181.admit; lax = _52_1181.lax; lax_universes = _52_1181.lax_universes; type_of = _52_1181.type_of; universe_of = _52_1181.universe_of; use_bv_sorts = _52_1181.use_bv_sorts; qname_and_index = _52_1181.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1191 -> (match (_52_1191) with
| (x, _52_1190) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1196 = ()
in (

let x = (

let _52_1198 = x
in {FStar_Syntax_Syntax.ppname = _52_1198.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1198.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1208 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1210 = env
in {solver = _52_1210.solver; range = _52_1210.range; curmodule = _52_1210.curmodule; gamma = []; gamma_cache = _52_1210.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1210.sigtab; is_pattern = _52_1210.is_pattern; instantiate_imp = _52_1210.instantiate_imp; effects = _52_1210.effects; generalize = _52_1210.generalize; letrecs = _52_1210.letrecs; top_level = _52_1210.top_level; check_uvars = _52_1210.check_uvars; use_eq = _52_1210.use_eq; is_iface = _52_1210.is_iface; admit = _52_1210.admit; lax = _52_1210.lax; lax_universes = _52_1210.lax_universes; type_of = _52_1210.type_of; universe_of = _52_1210.universe_of; use_bv_sorts = _52_1210.use_bv_sorts; qname_and_index = _52_1210.qname_and_index})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1218 = env
in {solver = _52_1218.solver; range = _52_1218.range; curmodule = _52_1218.curmodule; gamma = _52_1218.gamma; gamma_cache = _52_1218.gamma_cache; modules = _52_1218.modules; expected_typ = Some (t); sigtab = _52_1218.sigtab; is_pattern = _52_1218.is_pattern; instantiate_imp = _52_1218.instantiate_imp; effects = _52_1218.effects; generalize = _52_1218.generalize; letrecs = _52_1218.letrecs; top_level = _52_1218.top_level; check_uvars = _52_1218.check_uvars; use_eq = false; is_iface = _52_1218.is_iface; admit = _52_1218.admit; lax = _52_1218.lax; lax_universes = _52_1218.lax_universes; type_of = _52_1218.type_of; universe_of = _52_1218.universe_of; use_bv_sorts = _52_1218.use_bv_sorts; qname_and_index = _52_1218.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _149_1190 = (expected_typ env)
in (((

let _52_1225 = env
in {solver = _52_1225.solver; range = _52_1225.range; curmodule = _52_1225.curmodule; gamma = _52_1225.gamma; gamma_cache = _52_1225.gamma_cache; modules = _52_1225.modules; expected_typ = None; sigtab = _52_1225.sigtab; is_pattern = _52_1225.is_pattern; instantiate_imp = _52_1225.instantiate_imp; effects = _52_1225.effects; generalize = _52_1225.generalize; letrecs = _52_1225.letrecs; top_level = _52_1225.top_level; check_uvars = _52_1225.check_uvars; use_eq = false; is_iface = _52_1225.is_iface; admit = _52_1225.admit; lax = _52_1225.lax; lax_universes = _52_1225.lax_universes; type_of = _52_1225.type_of; universe_of = _52_1225.universe_of; use_bv_sorts = _52_1225.use_bv_sorts; qname_and_index = _52_1225.qname_and_index})), (_149_1190))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _149_1196 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1232, se) -> begin
(se)::[]
end
| _52_1237 -> begin
[]
end))))
in (FStar_All.pipe_right _149_1196 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1239 = (add_sigelts env sigs)
in (

let _52_1241 = env
in {solver = _52_1241.solver; range = _52_1241.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1241.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1241.expected_typ; sigtab = _52_1241.sigtab; is_pattern = _52_1241.is_pattern; instantiate_imp = _52_1241.instantiate_imp; effects = _52_1241.effects; generalize = _52_1241.generalize; letrecs = _52_1241.letrecs; top_level = _52_1241.top_level; check_uvars = _52_1241.check_uvars; use_eq = _52_1241.use_eq; is_iface = _52_1241.is_iface; admit = _52_1241.admit; lax = _52_1241.lax; lax_universes = _52_1241.lax_universes; type_of = _52_1241.type_of; universe_of = _52_1241.universe_of; use_bv_sorts = _52_1241.use_bv_sorts; qname_and_index = _52_1241.qname_and_index})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1254))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _149_1208 = (let _149_1207 = (FStar_Syntax_Free.uvars t)
in (ext out _149_1207))
in (aux _149_1208 tl))
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
(let _149_1220 = (let _149_1219 = (FStar_Syntax_Free.univs t)
in (ext out _149_1219))
in (aux _149_1220 tl))
end
| (Binding_sig (_52_1324))::_52_1322 -> begin
out
end))
in (aux no_univs env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _52_11 -> (match (_52_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _149_1227 = (let _149_1226 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _149_1226 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _149_1227 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1356) -> begin
(FStar_List.append lids keys)
end
| _52_1360 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1362 v keys -> (let _149_1250 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _149_1250 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1366 -> ()); push = (fun _52_1368 -> ()); pop = (fun _52_1370 -> ()); mark = (fun _52_1372 -> ()); reset_mark = (fun _52_1374 -> ()); commit_mark = (fun _52_1376 -> ()); encode_modul = (fun _52_1378 _52_1380 -> ()); encode_sig = (fun _52_1382 _52_1384 -> ()); solve = (fun _52_1386 _52_1388 _52_1390 -> ()); is_trivial = (fun _52_1392 _52_1394 -> false); finish = (fun _52_1396 -> ()); refresh = (fun _52_1397 -> ())}




