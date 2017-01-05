
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
| Binding_var (_54_16) -> begin
_54_16
end))


let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_54_19) -> begin
_54_19
end))


let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_54_22) -> begin
_54_22
end))


let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_54_25) -> begin
_54_25
end))


let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_54_28) -> begin
_54_28
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
| Unfold (_54_31) -> begin
_54_31
end))


type mlift =
FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ


type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ}


let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkedge"))))


type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkeffects"))))


type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either


type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) Prims.option} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv"))))


let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mksolver_t"))))


let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkguard_t"))))


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
| _54_108 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun _54_109 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _54_110 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _153_422 = (new_gamma_cache ())
in (let _153_421 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _153_422; modules = []; expected_typ = None; sigtab = _153_421; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun _54_126 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| [] -> begin
(failwith "Empty query indices!")
end
| _54_129 -> begin
(let _153_487 = (let _153_486 = (let _153_484 = (FStar_ST.read query_indices)
in (FStar_List.hd _153_484))
in (let _153_485 = (FStar_ST.read query_indices)
in (_153_486)::_153_485))
in (FStar_ST.op_Colon_Equals query_indices _153_487))
end)
end))
in (

let pop_query_indices = (fun _54_131 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices tl)
end)
end))
in (

let add_query_index = (fun _54_139 -> (match (_54_139) with
| (l, n) -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n)))::hd)::tl))
end
| _54_144 -> begin
(failwith "Empty query indices")
end)
end))
in (

let peek_query_indices = (fun _54_146 -> (match (()) with
| () -> begin
(let _153_494 = (FStar_ST.read query_indices)
in (FStar_List.hd _153_494))
end))
in (

let commit_query_index_mark = (fun _54_148 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::(_54_151)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices ((hd)::tl))
end
| _54_156 -> begin
(failwith "Unmarked query index stack")
end)
end))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> (

let _54_160 = (let _153_500 = (let _153_499 = (FStar_ST.read stack)
in (env)::_153_499)
in (FStar_ST.op_Colon_Equals stack _153_500))
in (

let _54_162 = env
in (let _153_502 = (FStar_Util.smap_copy (gamma_cache env))
in (let _153_501 = (FStar_Util.smap_copy (sigtab env))
in {solver = _54_162.solver; range = _54_162.range; curmodule = _54_162.curmodule; gamma = _54_162.gamma; gamma_cache = _153_502; modules = _54_162.modules; expected_typ = _54_162.expected_typ; sigtab = _153_501; is_pattern = _54_162.is_pattern; instantiate_imp = _54_162.instantiate_imp; effects = _54_162.effects; generalize = _54_162.generalize; letrecs = _54_162.letrecs; top_level = _54_162.top_level; check_uvars = _54_162.check_uvars; use_eq = _54_162.use_eq; is_iface = _54_162.is_iface; admit = _54_162.admit; lax = _54_162.lax; lax_universes = _54_162.lax_universes; type_of = _54_162.type_of; universe_of = _54_162.universe_of; use_bv_sorts = _54_162.use_bv_sorts; qname_and_index = _54_162.qname_and_index})))))
in (

let pop_stack = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _54_169 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _54_172 -> begin
(failwith "Impossible: Too many pops")
end))
in (

let push = (fun env -> (

let _54_175 = (push_query_indices ())
in (push_stack env)))
in (

let pop = (fun env -> (

let _54_179 = (pop_query_indices ())
in (pop_stack env)))
in (

let mark = (fun env -> (

let _54_183 = (push_query_indices ())
in (push_stack env)))
in (

let commit_mark = (fun env -> (

let _54_187 = (commit_query_index_mark ())
in (

let _54_189 = (let _153_513 = (pop_stack env)
in (Prims.ignore _153_513))
in env)))
in (

let reset_mark = (fun env -> (

let _54_193 = (pop_query_indices ())
in (pop_stack env)))
in (

let incr_query_index = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(match ((FStar_All.pipe_right qix (FStar_List.tryFind (fun _54_206 -> (match (_54_206) with
| (m, _54_205) -> begin
(FStar_Ident.lid_equals l m)
end))))) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in (

let _54_209 = (add_query_index ((l), (next)))
in (

let _54_211 = env
in {solver = _54_211.solver; range = _54_211.range; curmodule = _54_211.curmodule; gamma = _54_211.gamma; gamma_cache = _54_211.gamma_cache; modules = _54_211.modules; expected_typ = _54_211.expected_typ; sigtab = _54_211.sigtab; is_pattern = _54_211.is_pattern; instantiate_imp = _54_211.instantiate_imp; effects = _54_211.effects; generalize = _54_211.generalize; letrecs = _54_211.letrecs; top_level = _54_211.top_level; check_uvars = _54_211.check_uvars; use_eq = _54_211.use_eq; is_iface = _54_211.is_iface; admit = _54_211.admit; lax = _54_211.lax; lax_universes = _54_211.lax_universes; type_of = _54_211.type_of; universe_of = _54_211.universe_of; use_bv_sorts = _54_211.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end
| Some (_54_214, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in (

let _54_219 = (add_query_index ((l), (next)))
in (

let _54_221 = env
in {solver = _54_221.solver; range = _54_221.range; curmodule = _54_221.curmodule; gamma = _54_221.gamma; gamma_cache = _54_221.gamma_cache; modules = _54_221.modules; expected_typ = _54_221.expected_typ; sigtab = _54_221.sigtab; is_pattern = _54_221.is_pattern; instantiate_imp = _54_221.instantiate_imp; effects = _54_221.effects; generalize = _54_221.generalize; letrecs = _54_221.letrecs; top_level = _54_221.top_level; check_uvars = _54_221.check_uvars; use_eq = _54_221.use_eq; is_iface = _54_221.is_iface; admit = _54_221.admit; lax = _54_221.lax; lax_universes = _54_221.lax_universes; type_of = _54_221.type_of; universe_of = _54_221.universe_of; use_bv_sorts = _54_221.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end)
end)))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop; es_incr_query_index = incr_query_index})))))))))))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _54_225 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _54_228 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _54_231 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _54_234 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _54_238 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let cleanup_interactive : env  ->  Prims.unit = (fun env -> (env.solver.pop ""))


let incr_query_index : env  ->  env = (fun env -> (stack_ops.es_incr_query_index env))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _54_246 = e
in {solver = _54_246.solver; range = r; curmodule = _54_246.curmodule; gamma = _54_246.gamma; gamma_cache = _54_246.gamma_cache; modules = _54_246.modules; expected_typ = _54_246.expected_typ; sigtab = _54_246.sigtab; is_pattern = _54_246.is_pattern; instantiate_imp = _54_246.instantiate_imp; effects = _54_246.effects; generalize = _54_246.generalize; letrecs = _54_246.letrecs; top_level = _54_246.top_level; check_uvars = _54_246.check_uvars; use_eq = _54_246.use_eq; is_iface = _54_246.is_iface; admit = _54_246.admit; lax = _54_246.lax; lax_universes = _54_246.lax_universes; type_of = _54_246.type_of; universe_of = _54_246.universe_of; use_bv_sorts = _54_246.use_bv_sorts; qname_and_index = _54_246.qname_and_index})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _54_253 = env
in {solver = _54_253.solver; range = _54_253.range; curmodule = lid; gamma = _54_253.gamma; gamma_cache = _54_253.gamma_cache; modules = _54_253.modules; expected_typ = _54_253.expected_typ; sigtab = _54_253.sigtab; is_pattern = _54_253.is_pattern; instantiate_imp = _54_253.instantiate_imp; effects = _54_253.effects; generalize = _54_253.generalize; letrecs = _54_253.letrecs; top_level = _54_253.top_level; check_uvars = _54_253.check_uvars; use_eq = _54_253.use_eq; is_iface = _54_253.is_iface; admit = _54_253.admit; lax = _54_253.lax; lax_universes = _54_253.lax_universes; type_of = _54_253.type_of; universe_of = _54_253.universe_of; use_bv_sorts = _54_253.use_bv_sorts; qname_and_index = _54_253.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _153_568 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _153_568)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _54_262 -> (match (()) with
| () -> begin
(let _153_571 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_153_571))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _54_274) -> begin
(

let _54_276 = ()
in (

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _153_578 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_153_578))))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _54_1 -> (match (_54_1) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _54_289 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let _54_296 = (inst_tscheme t)
in (match (_54_296) with
| (us, t) -> begin
(let _153_586 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (_153_586)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _54_302 -> (match (_54_302) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _54_305 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _153_599 = (let _153_598 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _153_597 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _153_596 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _153_595 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _153_598 _153_597 _153_596 _153_595)))))
in (failwith _153_599))
end else begin
()
end
in (let _153_600 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _153_600))))
end
| _54_308 -> begin
(let _153_602 = (let _153_601 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _153_601))
in (failwith _153_602))
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
| ([], _54_319) -> begin
Maybe
end
| (_54_322, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _54_333 -> begin
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

let _54_339 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _54_2 -> (match (_54_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _153_622 = (let _153_621 = (inst_tscheme t)
in FStar_Util.Inl (_153_621))
in Some (_153_622))
end else begin
None
end
end
| Binding_sig (_54_348, FStar_Syntax_Syntax.Sig_bundle (ses, _54_351, _54_353, _54_355)) -> begin
(FStar_Util.find_map ses (fun se -> if (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
(cache (FStar_Util.Inr (((se), (None)))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_54_368) -> begin
Some (t)
end
| _54_371 -> begin
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
| _54_378 -> begin
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
| FStar_Syntax_Syntax.Sig_bundle (ses, _54_388, _54_390, _54_392) -> begin
(add_sigelts env ses)
end
| _54_396 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let _54_399 = (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _54_403) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| _54_409 -> begin
()
end)))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _54_3 -> (match (_54_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _54_418 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_54_422, (lb)::[]), _54_427, _54_429, _54_431, _54_433) -> begin
(let _153_645 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_153_645))
end
| FStar_Syntax_Syntax.Sig_let ((_54_437, lbs), _54_441, _54_443, _54_445, _54_447) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_54_452) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _153_647 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_153_647))
end else begin
None
end
end)))
end
| _54_457 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _54_461) -> begin
(let _153_653 = (let _153_652 = (let _153_651 = (let _153_650 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _153_650))
in ((ne.FStar_Syntax_Syntax.univs), (_153_651)))
in (inst_tscheme _153_652))
in Some (_153_653))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _54_468, _54_470, _54_472, _54_474) -> begin
(let _153_657 = (let _153_656 = (let _153_655 = (let _153_654 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _153_654))
in ((us), (_153_655)))
in (inst_tscheme _153_656))
in Some (_153_657))
end
| _54_478 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun _54_4 -> (match (_54_4) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_54_485, uvs, t, _54_489, _54_491, _54_493, _54_495, _54_497), None) -> begin
(let _153_664 = (inst_tscheme ((uvs), (t)))
in Some (_153_664))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _54_508), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _153_665 = (inst_tscheme ((uvs), (t)))
in Some (_153_665))
end else begin
None
end
end else begin
(let _153_666 = (inst_tscheme ((uvs), (t)))
in Some (_153_666))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _54_519, _54_521, _54_523, _54_525), None) -> begin
(match (tps) with
| [] -> begin
(let _153_668 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _153_667 -> Some (_153_667)) _153_668))
end
| _54_533 -> begin
(let _153_673 = (let _153_672 = (let _153_671 = (let _153_670 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _153_670))
in ((uvs), (_153_671)))
in (inst_tscheme _153_672))
in (FStar_All.pipe_left (fun _153_669 -> Some (_153_669)) _153_673))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _54_539, _54_541, _54_543, _54_545), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _153_675 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _153_674 -> Some (_153_674)) _153_675))
end
| _54_554 -> begin
(let _153_680 = (let _153_679 = (let _153_678 = (let _153_677 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _153_677))
in ((uvs), (_153_678)))
in (inst_tscheme_with _153_679 us))
in (FStar_All.pipe_left (fun _153_676 -> Some (_153_676)) _153_680))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_54_558), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _54_563 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _153_681 = (lookup_qname env lid)
in (FStar_Util.bind_opt _153_681 mapper))) with
| Some (us, t) -> begin
Some (((us), ((

let _54_569 = t
in {FStar_Syntax_Syntax.n = _54_569.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _54_569.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _54_569.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end)))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_54_576) -> begin
true
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _153_693 = (let _153_692 = (let _153_691 = (variable_not_found bv)
in (let _153_690 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_153_691), (_153_690))))
in FStar_Syntax_Syntax.Error (_153_692))
in (Prims.raise _153_693))
end
| Some (t) -> begin
(let _153_694 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range _153_694 t))
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (match ((try_lookup_lid_aux env l)) with
| None -> begin
None
end
| Some (us, t) -> begin
(let _153_700 = (let _153_699 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (_153_699)))
in Some (_153_700))
end))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _153_707 = (let _153_706 = (let _153_705 = (name_not_found l)
in ((_153_705), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_153_706))
in (Prims.raise _153_707))
end
| Some (us, t) -> begin
((us), (t))
end))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _54_5 -> (match (_54_5) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _54_603 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_54_607, uvs, t, q, _54_612), None)) -> begin
(let _153_722 = (let _153_721 = (let _153_720 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (_153_720)))
in ((_153_721), (q)))
in Some (_153_722))
end
| _54_620 -> begin
None
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_54_624, uvs, t, _54_628, _54_630), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| _54_638 -> begin
(let _153_729 = (let _153_728 = (let _153_727 = (name_not_found lid)
in ((_153_727), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_153_728))
in (Prims.raise _153_729))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_54_642, uvs, t, _54_646, _54_648, _54_650, _54_652, _54_654), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| _54_662 -> begin
(let _153_736 = (let _153_735 = (let _153_734 = (name_not_found lid)
in ((_153_734), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_153_735))
in (Prims.raise _153_736))
end))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_54_666, _54_668, _54_670, _54_672, _54_674, dcs, _54_677, _54_679), _54_683)) -> begin
dcs
end
| _54_688 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_54_692, _54_694, _54_696, l, _54_699, _54_701, _54_703, _54_705), _54_709)) -> begin
l
end
| _54_714 -> begin
(let _153_746 = (let _153_745 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _153_745))
in (failwith _153_746))
end))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_54_727, lbs), _54_731, _54_733, quals, _54_736) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _153_759 = (let _153_758 = (let _153_757 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) _153_757))
in ((lb.FStar_Syntax_Syntax.lbunivs), (_153_758)))
in Some (_153_759))
end else begin
None
end)))
end
| _54_742 -> begin
None
end)
end
| _54_744 -> begin
None
end)))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_54_754, t) -> begin
(let _153_764 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (_153_764))
end)
end
| _54_759 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _153_771 = (let _153_770 = (let _153_769 = (name_not_found ftv)
in ((_153_769), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_153_770))
in (Prims.raise _153_771))
end
| Some (k) -> begin
k
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (match ((lookup_qname env lid0)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _54_774, _54_776), None)) -> begin
(

let lid = (let _153_778 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid _153_778))
in if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_6 -> (match (_54_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _54_787 -> begin
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
(let _153_782 = (let _153_781 = (FStar_Syntax_Print.lid_to_string lid)
in (let _153_780 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" _153_781 _153_780)))
in (failwith _153_782))
end
end
in (match (((binders), (univs))) with
| ([], _54_791) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (_54_794, (_54_801)::(_54_798)::_54_796) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _153_785 = (let _153_784 = (FStar_Syntax_Print.lid_to_string lid)
in (let _153_783 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _153_784 _153_783)))
in (failwith _153_785))
end
| _54_805 -> begin
(

let _54_809 = (let _153_787 = (let _153_786 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_153_786)))
in (inst_tscheme_with _153_787 insts))
in (match (_54_809) with
| (_54_807, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (match ((let _153_788 = (FStar_Syntax_Subst.compress t)
in _153_788.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| _54_816 -> begin
(failwith "Impossible")
end))
end))
end))
end)
end
| _54_818 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)) with
| None -> begin
None
end
| Some (_54_826, c) -> begin
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

let _54_840 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in (FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l))))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l = (norm_eff_name env l)
in (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, _54_848), _54_852)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| _54_857 -> begin
[]
end)))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _54_862 -> (match (()) with
| () -> begin
(let _153_809 = (let _153_808 = (FStar_Util.string_of_int i)
in (let _153_807 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _153_808 _153_807)))
in (failwith _153_809))
end))
in (

let _54_866 = (lookup_datacon env lid)
in (match (_54_866) with
| (_54_864, t) -> begin
(match ((let _153_810 = (FStar_Syntax_Subst.compress t)
in _153_810.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _54_869) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _153_811 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _153_811 Prims.fst)))
end
end
| _54_874 -> begin
(fail ())
end)
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_54_878, _54_880, _54_882, quals, _54_885), _54_889)) -> begin
(FStar_Util.for_some (fun _54_7 -> (match (_54_7) with
| FStar_Syntax_Syntax.Projector (_54_895) -> begin
true
end
| _54_898 -> begin
false
end)) quals)
end
| _54_900 -> begin
false
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_54_904, _54_906, _54_908, _54_910, _54_912, _54_914, _54_916, _54_918), _54_922)) -> begin
true
end
| _54_927 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_54_931, _54_933, _54_935, _54_937, _54_939, _54_941, tags, _54_944), _54_948)) -> begin
(FStar_Util.for_some (fun _54_8 -> (match (_54_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _54_960 -> begin
false
end)) tags)
end
| _54_962 -> begin
false
end))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_let (_54_966, _54_968, _54_970, tags, _54_973), _54_977)) -> begin
(FStar_Util.for_some (fun _54_9 -> (match (_54_9) with
| FStar_Syntax_Syntax.Action (_54_983) -> begin
true
end
| _54_986 -> begin
false
end)) tags)
end
| _54_988 -> begin
false
end))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (match ((let _153_835 = (FStar_Syntax_Util.un_uinst head)
in _153_835.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _54_995 -> begin
false
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _54_10 -> (match (_54_10) with
| FStar_Util.Inl (_54_1000) -> begin
Some (false)
end
| FStar_Util.Inr (se, _54_1004) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_54_1008, _54_1010, _54_1012, qs, _54_1015) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_54_1019) -> begin
Some (true)
end
| _54_1022 -> begin
Some (false)
end)
end))
in (match ((let _153_842 = (lookup_qname env lid)
in (FStar_Util.bind_opt _153_842 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _153_854 = (let _153_853 = (let _153_852 = (name_not_found l)
in ((_153_852), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_153_853))
in (Prims.raise _153_854))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _54_1054 -> (match (_54_1054) with
| (m1, m2, _54_1049, _54_1051, _54_1053) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _153_930 = (let _153_929 = (let _153_928 = (let _153_927 = (FStar_Syntax_Print.lid_to_string l1)
in (let _153_926 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _153_927 _153_926)))
in ((_153_928), (env.range)))
in FStar_Syntax_Syntax.Error (_153_929))
in (Prims.raise _153_930))
end
| Some (_54_1057, _54_1059, m3, j1, j2) -> begin
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
(let _153_945 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith _153_945))
end
| Some (md) -> begin
(

let _54_1080 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_54_1080) with
| (_54_1078, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _54_1089))::((wp, _54_1085))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _54_1097 -> begin
(failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _54_1104) -> begin
(

let effects = (

let _54_1107 = env.effects
in {decls = (ne)::env.effects.decls; order = _54_1107.order; joins = _54_1107.joins})
in (

let _54_1110 = env
in {solver = _54_1110.solver; range = _54_1110.range; curmodule = _54_1110.curmodule; gamma = _54_1110.gamma; gamma_cache = _54_1110.gamma_cache; modules = _54_1110.modules; expected_typ = _54_1110.expected_typ; sigtab = _54_1110.sigtab; is_pattern = _54_1110.is_pattern; instantiate_imp = _54_1110.instantiate_imp; effects = effects; generalize = _54_1110.generalize; letrecs = _54_1110.letrecs; top_level = _54_1110.top_level; check_uvars = _54_1110.check_uvars; use_eq = _54_1110.use_eq; is_iface = _54_1110.is_iface; admit = _54_1110.admit; lax = _54_1110.lax; lax_universes = _54_1110.lax_universes; type_of = _54_1110.type_of; universe_of = _54_1110.universe_of; use_bv_sorts = _54_1110.use_bv_sorts; qname_and_index = _54_1110.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _54_1114) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _153_960 = (e1.mlift r wp1)
in (e2.mlift r _153_960)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _54_1129 = (inst_tscheme lift_t)
in (match (_54_1129) with
| (_54_1127, lift_t) -> begin
(let _153_972 = (let _153_971 = (let _153_970 = (let _153_969 = (FStar_Syntax_Syntax.as_arg r)
in (let _153_968 = (let _153_967 = (FStar_Syntax_Syntax.as_arg wp1)
in (_153_967)::[])
in (_153_969)::_153_968))
in ((lift_t), (_153_970)))
in FStar_Syntax_Syntax.Tm_app (_153_971))
in (FStar_Syntax_Syntax.mk _153_972 None wp1.FStar_Syntax_Syntax.pos))
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

let arg = (let _153_989 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _153_989 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _153_990 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _153_990 FStar_Syntax_Syntax.Delta_constant None))
in (let _153_991 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _153_991)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _54_1150 -> (match (_54_1150) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _153_997 -> Some (_153_997)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _153_1005 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _153_1004 = (find_edge order ((i), (k)))
in (let _153_1003 = (find_edge order ((k), (j)))
in ((_153_1004), (_153_1003))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _54_1162 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _153_1005))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let _54_1168 = (FStar_All.pipe_right order (FStar_List.iter (fun edge -> if ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (let _153_1009 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right _153_1009 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))) then begin
(let _153_1013 = (let _153_1012 = (let _153_1011 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (let _153_1010 = (get_range env)
in ((_153_1011), (_153_1010))))
in FStar_Syntax_Syntax.Error (_153_1012))
in (Prims.raise _153_1013))
end else begin
()
end)))
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _153_1103 = (find_edge order ((i), (k)))
in (let _153_1102 = (find_edge order ((j), (k)))
in ((_153_1103), (_153_1102))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _54_1182, _54_1184) -> begin
if ((let _153_1104 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _153_1104)) && (not ((let _153_1105 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _153_1105))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _54_1188 -> begin
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

let _54_1197 = env.effects
in {decls = _54_1197.decls; order = order; joins = joins})
in (

let _54_1200 = env
in {solver = _54_1200.solver; range = _54_1200.range; curmodule = _54_1200.curmodule; gamma = _54_1200.gamma; gamma_cache = _54_1200.gamma_cache; modules = _54_1200.modules; expected_typ = _54_1200.expected_typ; sigtab = _54_1200.sigtab; is_pattern = _54_1200.is_pattern; instantiate_imp = _54_1200.instantiate_imp; effects = effects; generalize = _54_1200.generalize; letrecs = _54_1200.letrecs; top_level = _54_1200.top_level; check_uvars = _54_1200.check_uvars; use_eq = _54_1200.use_eq; is_iface = _54_1200.is_iface; admit = _54_1200.admit; lax = _54_1200.lax; lax_universes = _54_1200.lax_universes; type_of = _54_1200.type_of; universe_of = _54_1200.universe_of; use_bv_sorts = _54_1200.use_bv_sorts; qname_and_index = _54_1200.qname_and_index})))))))))))))))
end
| _54_1203 -> begin
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
(let _153_1154 = (push x rest)
in (local)::_153_1154)
end))
in (

let _54_1225 = env
in (let _153_1155 = (push s env.gamma)
in {solver = _54_1225.solver; range = _54_1225.range; curmodule = _54_1225.curmodule; gamma = _153_1155; gamma_cache = _54_1225.gamma_cache; modules = _54_1225.modules; expected_typ = _54_1225.expected_typ; sigtab = _54_1225.sigtab; is_pattern = _54_1225.is_pattern; instantiate_imp = _54_1225.instantiate_imp; effects = _54_1225.effects; generalize = _54_1225.generalize; letrecs = _54_1225.letrecs; top_level = _54_1225.top_level; check_uvars = _54_1225.check_uvars; use_eq = _54_1225.use_eq; is_iface = _54_1225.is_iface; admit = _54_1225.admit; lax = _54_1225.lax; lax_universes = _54_1225.lax_universes; type_of = _54_1225.type_of; universe_of = _54_1225.universe_of; use_bv_sorts = _54_1225.use_bv_sorts; qname_and_index = _54_1225.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _54_1236 = env
in {solver = _54_1236.solver; range = _54_1236.range; curmodule = _54_1236.curmodule; gamma = (b)::env.gamma; gamma_cache = _54_1236.gamma_cache; modules = _54_1236.modules; expected_typ = _54_1236.expected_typ; sigtab = _54_1236.sigtab; is_pattern = _54_1236.is_pattern; instantiate_imp = _54_1236.instantiate_imp; effects = _54_1236.effects; generalize = _54_1236.generalize; letrecs = _54_1236.letrecs; top_level = _54_1236.top_level; check_uvars = _54_1236.check_uvars; use_eq = _54_1236.use_eq; is_iface = _54_1236.is_iface; admit = _54_1236.admit; lax = _54_1236.lax; lax_universes = _54_1236.lax_universes; type_of = _54_1236.type_of; universe_of = _54_1236.universe_of; use_bv_sorts = _54_1236.use_bv_sorts; qname_and_index = _54_1236.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _54_1246 -> (match (_54_1246) with
| (x, _54_1245) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _54_1251 = ()
in (

let x = (

let _54_1253 = x
in {FStar_Syntax_Syntax.ppname = _54_1253.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_1253.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _54_1263 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _54_1265 = env
in {solver = _54_1265.solver; range = _54_1265.range; curmodule = _54_1265.curmodule; gamma = []; gamma_cache = _54_1265.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _54_1265.sigtab; is_pattern = _54_1265.is_pattern; instantiate_imp = _54_1265.instantiate_imp; effects = _54_1265.effects; generalize = _54_1265.generalize; letrecs = _54_1265.letrecs; top_level = _54_1265.top_level; check_uvars = _54_1265.check_uvars; use_eq = _54_1265.use_eq; is_iface = _54_1265.is_iface; admit = _54_1265.admit; lax = _54_1265.lax; lax_universes = _54_1265.lax_universes; type_of = _54_1265.type_of; universe_of = _54_1265.universe_of; use_bv_sorts = _54_1265.use_bv_sorts; qname_and_index = _54_1265.qname_and_index})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _54_1273 = env
in {solver = _54_1273.solver; range = _54_1273.range; curmodule = _54_1273.curmodule; gamma = _54_1273.gamma; gamma_cache = _54_1273.gamma_cache; modules = _54_1273.modules; expected_typ = Some (t); sigtab = _54_1273.sigtab; is_pattern = _54_1273.is_pattern; instantiate_imp = _54_1273.instantiate_imp; effects = _54_1273.effects; generalize = _54_1273.generalize; letrecs = _54_1273.letrecs; top_level = _54_1273.top_level; check_uvars = _54_1273.check_uvars; use_eq = false; is_iface = _54_1273.is_iface; admit = _54_1273.admit; lax = _54_1273.lax; lax_universes = _54_1273.lax_universes; type_of = _54_1273.type_of; universe_of = _54_1273.universe_of; use_bv_sorts = _54_1273.use_bv_sorts; qname_and_index = _54_1273.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _153_1208 = (expected_typ env)
in (((

let _54_1280 = env
in {solver = _54_1280.solver; range = _54_1280.range; curmodule = _54_1280.curmodule; gamma = _54_1280.gamma; gamma_cache = _54_1280.gamma_cache; modules = _54_1280.modules; expected_typ = None; sigtab = _54_1280.sigtab; is_pattern = _54_1280.is_pattern; instantiate_imp = _54_1280.instantiate_imp; effects = _54_1280.effects; generalize = _54_1280.generalize; letrecs = _54_1280.letrecs; top_level = _54_1280.top_level; check_uvars = _54_1280.check_uvars; use_eq = false; is_iface = _54_1280.is_iface; admit = _54_1280.admit; lax = _54_1280.lax; lax_universes = _54_1280.lax_universes; type_of = _54_1280.type_of; universe_of = _54_1280.universe_of; use_bv_sorts = _54_1280.use_bv_sorts; qname_and_index = _54_1280.qname_and_index})), (_153_1208))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _153_1214 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _54_11 -> (match (_54_11) with
| Binding_sig (_54_1287, se) -> begin
(se)::[]
end
| _54_1292 -> begin
[]
end))))
in (FStar_All.pipe_right _153_1214 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _54_1294 = (add_sigelts env sigs)
in (

let _54_1296 = env
in {solver = _54_1296.solver; range = _54_1296.range; curmodule = empty_lid; gamma = []; gamma_cache = _54_1296.gamma_cache; modules = (m)::env.modules; expected_typ = _54_1296.expected_typ; sigtab = _54_1296.sigtab; is_pattern = _54_1296.is_pattern; instantiate_imp = _54_1296.instantiate_imp; effects = _54_1296.effects; generalize = _54_1296.generalize; letrecs = _54_1296.letrecs; top_level = _54_1296.top_level; check_uvars = _54_1296.check_uvars; use_eq = _54_1296.use_eq; is_iface = _54_1296.is_iface; admit = _54_1296.admit; lax = _54_1296.lax; lax_universes = _54_1296.lax_universes; type_of = _54_1296.type_of; universe_of = _54_1296.universe_of; use_bv_sorts = _54_1296.use_bv_sorts; qname_and_index = _54_1296.qname_and_index})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_54_1309))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _153_1226 = (let _153_1225 = (FStar_Syntax_Free.uvars t)
in (ext out _153_1225))
in (aux _153_1226 tl))
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
(let _153_1238 = (let _153_1237 = (FStar_Syntax_Free.univs t)
in (ext out _153_1237))
in (aux _153_1238 tl))
end
| (Binding_sig (_54_1379))::_54_1377 -> begin
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
| (Binding_sig_inst (_54_1393))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(let _153_1249 = (FStar_Util.set_add uname out)
in (aux _153_1249 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _153_1251 = (let _153_1250 = (FStar_Syntax_Free.univnames t)
in (ext out _153_1250))
in (aux _153_1251 tl))
end
| (Binding_sig (_54_1420))::_54_1418 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _54_12 -> (match (_54_12) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _153_1258 = (let _153_1257 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _153_1257 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _153_1258 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _54_13 -> (match (_54_13) with
| Binding_sig (lids, _54_1452) -> begin
(FStar_List.append lids keys)
end
| _54_1456 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _54_1458 v keys -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)) keys)))


let dummy_solver : solver_t = {init = (fun _54_1462 -> ()); push = (fun _54_1464 -> ()); pop = (fun _54_1466 -> ()); mark = (fun _54_1468 -> ()); reset_mark = (fun _54_1470 -> ()); commit_mark = (fun _54_1472 -> ()); encode_modul = (fun _54_1474 _54_1476 -> ()); encode_sig = (fun _54_1478 _54_1480 -> ()); solve = (fun _54_1482 _54_1484 _54_1486 -> ()); is_trivial = (fun _54_1488 _54_1490 -> false); finish = (fun _54_1492 -> ()); refresh = (fun _54_1493 -> ())}




