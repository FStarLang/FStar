
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
| OnlyInline
| Unfold of FStar_Syntax_Syntax.delta_depth


let is_NoDelta = (fun _discr_ -> (match (_discr_) with
| NoDelta (_) -> begin
true
end
| _ -> begin
false
end))


let is_OnlyInline = (fun _discr_ -> (match (_discr_) with
| OnlyInline (_) -> begin
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
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _52_104 -> begin
false
end))


let glb_delta : delta_level  ->  delta_level  ->  delta_level = (fun d1 d2 -> (match (((d1), (d2))) with
| ((NoDelta, _)) | ((_, NoDelta)) -> begin
NoDelta
end
| ((OnlyInline, _)) | ((_, OnlyInline)) -> begin
OnlyInline
end
| (Unfold (l1), Unfold (l2)) -> begin
(

let rec aux = (fun l1 l2 -> (match (((l1), (l2))) with
| ((FStar_Syntax_Syntax.Delta_constant, _)) | ((_, FStar_Syntax_Syntax.Delta_constant)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| ((FStar_Syntax_Syntax.Delta_equational, l)) | ((l, FStar_Syntax_Syntax.Delta_equational)) -> begin
l
end
| (FStar_Syntax_Syntax.Delta_unfoldable (i), FStar_Syntax_Syntax.Delta_unfoldable (j)) -> begin
(

let k = if (i < j) then begin
i
end else begin
j
end
in FStar_Syntax_Syntax.Delta_unfoldable (k))
end
| (FStar_Syntax_Syntax.Delta_abstract (l1), _52_153) -> begin
(aux l1 l2)
end
| (_52_156, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _146_398 = (aux l1 l2)
in Unfold (_146_398)))
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun _52_160 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _52_161 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _146_430 = (new_gamma_cache ())
in (let _146_429 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _146_430; modules = []; expected_typ = None; sigtab = _146_429; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun _52_177 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| [] -> begin
(FStar_All.failwith "Empty query indices!")
end
| _52_180 -> begin
(let _146_495 = (let _146_494 = (let _146_492 = (FStar_ST.read query_indices)
in (FStar_List.hd _146_492))
in (let _146_493 = (FStar_ST.read query_indices)
in (_146_494)::_146_493))
in (FStar_ST.op_Colon_Equals query_indices _146_495))
end)
end))
in (

let pop_query_indices = (fun _52_182 -> (match (()) with
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

let add_query_index = (fun _52_190 -> (match (_52_190) with
| (l, n) -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n)))::hd)::tl))
end
| _52_195 -> begin
(FStar_All.failwith "Empty query indices")
end)
end))
in (

let peek_query_indices = (fun _52_197 -> (match (()) with
| () -> begin
(let _146_502 = (FStar_ST.read query_indices)
in (FStar_List.hd _146_502))
end))
in (

let commit_query_index_mark = (fun _52_199 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::(_52_202)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices ((hd)::tl))
end
| _52_207 -> begin
(FStar_All.failwith "Unmarked query index stack")
end)
end))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> (

let _52_211 = (let _146_508 = (let _146_507 = (FStar_ST.read stack)
in (env)::_146_507)
in (FStar_ST.op_Colon_Equals stack _146_508))
in (

let _52_213 = env
in (let _146_510 = (FStar_Util.smap_copy (gamma_cache env))
in (let _146_509 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_213.solver; range = _52_213.range; curmodule = _52_213.curmodule; gamma = _52_213.gamma; gamma_cache = _146_510; modules = _52_213.modules; expected_typ = _52_213.expected_typ; sigtab = _146_509; is_pattern = _52_213.is_pattern; instantiate_imp = _52_213.instantiate_imp; effects = _52_213.effects; generalize = _52_213.generalize; letrecs = _52_213.letrecs; top_level = _52_213.top_level; check_uvars = _52_213.check_uvars; use_eq = _52_213.use_eq; is_iface = _52_213.is_iface; admit = _52_213.admit; lax = _52_213.lax; lax_universes = _52_213.lax_universes; type_of = _52_213.type_of; universe_of = _52_213.universe_of; use_bv_sorts = _52_213.use_bv_sorts; qname_and_index = _52_213.qname_and_index})))))
in (

let pop_stack = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_220 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_223 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let push = (fun env -> (

let _52_226 = (push_query_indices ())
in (push_stack env)))
in (

let pop = (fun env -> (

let _52_230 = (pop_query_indices ())
in (pop_stack env)))
in (

let mark = (fun env -> (

let _52_234 = (push_query_indices ())
in (push_stack env)))
in (

let commit_mark = (fun env -> (

let _52_238 = (commit_query_index_mark ())
in (

let _52_240 = (let _146_521 = (pop_stack env)
in (Prims.ignore _146_521))
in env)))
in (

let reset_mark = (fun env -> (

let _52_244 = (pop_query_indices ())
in (pop_stack env)))
in (

let incr_query_index = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(match ((FStar_All.pipe_right qix (FStar_List.tryFind (fun _52_257 -> (match (_52_257) with
| (m, _52_256) -> begin
(FStar_Ident.lid_equals l m)
end))))) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in (

let _52_260 = (add_query_index ((l), (next)))
in (

let _52_262 = env
in {solver = _52_262.solver; range = _52_262.range; curmodule = _52_262.curmodule; gamma = _52_262.gamma; gamma_cache = _52_262.gamma_cache; modules = _52_262.modules; expected_typ = _52_262.expected_typ; sigtab = _52_262.sigtab; is_pattern = _52_262.is_pattern; instantiate_imp = _52_262.instantiate_imp; effects = _52_262.effects; generalize = _52_262.generalize; letrecs = _52_262.letrecs; top_level = _52_262.top_level; check_uvars = _52_262.check_uvars; use_eq = _52_262.use_eq; is_iface = _52_262.is_iface; admit = _52_262.admit; lax = _52_262.lax; lax_universes = _52_262.lax_universes; type_of = _52_262.type_of; universe_of = _52_262.universe_of; use_bv_sorts = _52_262.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end
| Some (_52_265, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in (

let _52_270 = (add_query_index ((l), (next)))
in (

let _52_272 = env
in {solver = _52_272.solver; range = _52_272.range; curmodule = _52_272.curmodule; gamma = _52_272.gamma; gamma_cache = _52_272.gamma_cache; modules = _52_272.modules; expected_typ = _52_272.expected_typ; sigtab = _52_272.sigtab; is_pattern = _52_272.is_pattern; instantiate_imp = _52_272.instantiate_imp; effects = _52_272.effects; generalize = _52_272.generalize; letrecs = _52_272.letrecs; top_level = _52_272.top_level; check_uvars = _52_272.check_uvars; use_eq = _52_272.use_eq; is_iface = _52_272.is_iface; admit = _52_272.admit; lax = _52_272.lax; lax_universes = _52_272.lax_universes; type_of = _52_272.type_of; universe_of = _52_272.universe_of; use_bv_sorts = _52_272.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end)
end)))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop; es_incr_query_index = incr_query_index})))))))))))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_276 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_279 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_282 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_285 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_289 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let incr_query_index : env  ->  env = (fun env -> (stack_ops.es_incr_query_index env))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_296 = e
in {solver = _52_296.solver; range = r; curmodule = _52_296.curmodule; gamma = _52_296.gamma; gamma_cache = _52_296.gamma_cache; modules = _52_296.modules; expected_typ = _52_296.expected_typ; sigtab = _52_296.sigtab; is_pattern = _52_296.is_pattern; instantiate_imp = _52_296.instantiate_imp; effects = _52_296.effects; generalize = _52_296.generalize; letrecs = _52_296.letrecs; top_level = _52_296.top_level; check_uvars = _52_296.check_uvars; use_eq = _52_296.use_eq; is_iface = _52_296.is_iface; admit = _52_296.admit; lax = _52_296.lax; lax_universes = _52_296.lax_universes; type_of = _52_296.type_of; universe_of = _52_296.universe_of; use_bv_sorts = _52_296.use_bv_sorts; qname_and_index = _52_296.qname_and_index})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_303 = env
in {solver = _52_303.solver; range = _52_303.range; curmodule = lid; gamma = _52_303.gamma; gamma_cache = _52_303.gamma_cache; modules = _52_303.modules; expected_typ = _52_303.expected_typ; sigtab = _52_303.sigtab; is_pattern = _52_303.is_pattern; instantiate_imp = _52_303.instantiate_imp; effects = _52_303.effects; generalize = _52_303.generalize; letrecs = _52_303.letrecs; top_level = _52_303.top_level; check_uvars = _52_303.check_uvars; use_eq = _52_303.use_eq; is_iface = _52_303.is_iface; admit = _52_303.admit; lax = _52_303.lax; lax_universes = _52_303.lax_universes; type_of = _52_303.type_of; universe_of = _52_303.universe_of; use_bv_sorts = _52_303.use_bv_sorts; qname_and_index = _52_303.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _146_574 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _146_574)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _52_312 -> (match (()) with
| () -> begin
(let _146_577 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_146_577))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _52_324) -> begin
(

let _52_326 = ()
in (

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _146_584 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_146_584))))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_339 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let _52_346 = (inst_tscheme t)
in (match (_52_346) with
| (us, t) -> begin
(let _146_592 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (_146_592)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_352 -> (match (_52_352) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_355 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _146_605 = (let _146_604 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _146_603 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _146_602 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_601 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _146_604 _146_603 _146_602 _146_601)))))
in (FStar_All.failwith _146_605))
end else begin
()
end
in (let _146_606 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _146_606))))
end
| _52_358 -> begin
(let _146_608 = (let _146_607 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _146_607))
in (FStar_All.failwith _146_608))
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
| ([], _52_369) -> begin
Maybe
end
| (_52_372, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_383 -> begin
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

let _52_389 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _146_628 = (let _146_627 = (inst_tscheme t)
in FStar_Util.Inl (_146_627))
in Some (_146_628))
end else begin
None
end
end
| Binding_sig (_52_398, FStar_Syntax_Syntax.Sig_bundle (ses, _52_401, _52_403, _52_405)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _146_630 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _146_630 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr (((se), (None)))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_418) -> begin
Some (t)
end
| _52_421 -> begin
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
| _52_428 -> begin
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
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_438, _52_440, _52_442) -> begin
(add_sigelts env ses)
end
| _52_446 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let _52_449 = (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_453) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| _52_459 -> begin
()
end)))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_3 -> (match (_52_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_468 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_472, (lb)::[]), _52_477, _52_479, _52_481) -> begin
(let _146_652 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_146_652))
end
| FStar_Syntax_Syntax.Sig_let ((_52_485, lbs), _52_489, _52_491, _52_493) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_498) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _146_654 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_146_654))
end else begin
None
end
end)))
end
| _52_503 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_507) -> begin
(let _146_660 = (let _146_659 = (let _146_658 = (let _146_657 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _146_657))
in ((ne.FStar_Syntax_Syntax.univs), (_146_658)))
in (inst_tscheme _146_659))
in Some (_146_660))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_514, _52_516, _52_518) -> begin
(let _146_664 = (let _146_663 = (let _146_662 = (let _146_661 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _146_661))
in ((us), (_146_662)))
in (inst_tscheme _146_663))
in Some (_146_664))
end
| _52_522 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun _52_4 -> (match (_52_4) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_529, uvs, t, _52_533, _52_535, _52_537, _52_539, _52_541), None) -> begin
(let _146_671 = (inst_tscheme ((uvs), (t)))
in Some (_146_671))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_552), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _146_672 = (inst_tscheme ((uvs), (t)))
in Some (_146_672))
end else begin
None
end
end else begin
(let _146_673 = (inst_tscheme ((uvs), (t)))
in Some (_146_673))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_563, _52_565, _52_567, _52_569), None) -> begin
(match (tps) with
| [] -> begin
(let _146_675 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _146_674 -> Some (_146_674)) _146_675))
end
| _52_577 -> begin
(let _146_680 = (let _146_679 = (let _146_678 = (let _146_677 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _146_677))
in ((uvs), (_146_678)))
in (inst_tscheme _146_679))
in (FStar_All.pipe_left (fun _146_676 -> Some (_146_676)) _146_680))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_583, _52_585, _52_587, _52_589), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _146_682 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _146_681 -> Some (_146_681)) _146_682))
end
| _52_598 -> begin
(let _146_687 = (let _146_686 = (let _146_685 = (let _146_684 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _146_684))
in ((uvs), (_146_685)))
in (inst_tscheme_with _146_686 us))
in (FStar_All.pipe_left (fun _146_683 -> Some (_146_683)) _146_687))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_602), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_607 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _146_688 = (lookup_qname env lid)
in (FStar_Util.bind_opt _146_688 mapper))) with
| Some (us, t) -> begin
Some (((us), ((

let _52_613 = t
in {FStar_Syntax_Syntax.n = _52_613.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_613.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_613.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end)))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_52_620) -> begin
true
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _146_700 = (let _146_699 = (let _146_698 = (variable_not_found bv)
in (let _146_697 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_146_698), (_146_697))))
in FStar_Syntax_Syntax.Error (_146_699))
in (Prims.raise _146_700))
end
| Some (t) -> begin
(let _146_701 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range _146_701 t))
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (match ((try_lookup_lid_aux env l)) with
| None -> begin
None
end
| Some (us, t) -> begin
(let _146_707 = (let _146_706 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (_146_706)))
in Some (_146_707))
end))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _146_714 = (let _146_713 = (let _146_712 = (name_not_found l)
in ((_146_712), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_146_713))
in (Prims.raise _146_714))
end
| Some (us, t) -> begin
((us), (t))
end))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_5 -> (match (_52_5) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_647 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_651, uvs, t, q, _52_656), None)) -> begin
(let _146_729 = (let _146_728 = (let _146_727 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (_146_727)))
in ((_146_728), (q)))
in Some (_146_729))
end
| _52_664 -> begin
None
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_668, uvs, t, _52_672, _52_674), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| _52_682 -> begin
(let _146_736 = (let _146_735 = (let _146_734 = (name_not_found lid)
in ((_146_734), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_146_735))
in (Prims.raise _146_736))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_686, uvs, t, _52_690, _52_692, _52_694, _52_696, _52_698), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| _52_706 -> begin
(let _146_743 = (let _146_742 = (let _146_741 = (name_not_found lid)
in ((_146_741), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_146_742))
in (Prims.raise _146_743))
end))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_710, _52_712, _52_714, _52_716, _52_718, dcs, _52_721, _52_723), _52_727)) -> begin
dcs
end
| _52_732 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_736, _52_738, _52_740, l, _52_743, _52_745, _52_747, _52_749), _52_753)) -> begin
l
end
| _52_758 -> begin
(let _146_753 = (let _146_752 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _146_752))
in (FStar_All.failwith _146_753))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_768, lbs), _52_772, _52_774, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _146_763 = (let _146_762 = (let _146_761 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) _146_761))
in ((lb.FStar_Syntax_Syntax.lbunivs), (_146_762)))
in Some (_146_763))
end else begin
None
end)))
end
| _52_781 -> begin
None
end)
end
| _52_783 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_793, t) -> begin
(let _146_768 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (_146_768))
end)
end
| _52_798 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _146_775 = (let _146_774 = (let _146_773 = (name_not_found ftv)
in ((_146_773), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_146_774))
in (Prims.raise _146_775))
end
| Some (k) -> begin
k
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (match ((lookup_qname env lid0)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_813), None)) -> begin
(

let lid = (let _146_782 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid _146_782))
in if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_6 -> (match (_52_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_824 -> begin
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
(let _146_786 = (let _146_785 = (FStar_Syntax_Print.lid_to_string lid)
in (let _146_784 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" _146_785 _146_784)))
in (FStar_All.failwith _146_786))
end
end
in (match (((binders), (univs))) with
| ([], _52_828) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_831, (_52_838)::(_52_835)::_52_833) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _146_789 = (let _146_788 = (FStar_Syntax_Print.lid_to_string lid)
in (let _146_787 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _146_788 _146_787)))
in (FStar_All.failwith _146_789))
end
| _52_842 -> begin
(

let _52_846 = (let _146_791 = (let _146_790 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_146_790)))
in (inst_tscheme_with _146_791 insts))
in (match (_52_846) with
| (_52_844, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (match ((let _146_792 = (FStar_Syntax_Subst.compress t)
in _146_792.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| _52_853 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))
end)
end
| _52_855 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)) with
| None -> begin
None
end
| Some (_52_863, c) -> begin
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

let _52_877 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in (FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l))))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l = (norm_eff_name env l)
in (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, _52_885), _52_889)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| _52_894 -> begin
[]
end)))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_899 -> (match (()) with
| () -> begin
(let _146_813 = (let _146_812 = (FStar_Util.string_of_int i)
in (let _146_811 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _146_812 _146_811)))
in (FStar_All.failwith _146_813))
end))
in (

let _52_903 = (lookup_datacon env lid)
in (match (_52_903) with
| (_52_901, t) -> begin
(match ((let _146_814 = (FStar_Syntax_Subst.compress t)
in _146_814.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_906) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _146_815 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _146_815 Prims.fst)))
end
end
| _52_911 -> begin
(fail ())
end)
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_915, _52_917, _52_919, quals, _52_922), _52_926)) -> begin
(FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Projector (_52_932) -> begin
true
end
| _52_935 -> begin
false
end)) quals)
end
| _52_937 -> begin
false
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_941, _52_943, _52_945, _52_947, _52_949, _52_951, _52_953, _52_955), _52_959)) -> begin
true
end
| _52_964 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_968, _52_970, _52_972, _52_974, _52_976, _52_978, tags, _52_981), _52_985)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_997 -> begin
false
end)) tags)
end
| _52_999 -> begin
false
end))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (match ((let _146_834 = (FStar_Syntax_Util.un_uinst head)
in _146_834.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_1006 -> begin
false
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_9 -> (match (_52_9) with
| FStar_Util.Inl (_52_1011) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_1015) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_1019, _52_1021, _52_1023, qs, _52_1026) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_1030) -> begin
Some (true)
end
| _52_1033 -> begin
Some (false)
end)
end))
in (match ((let _146_841 = (lookup_qname env lid)
in (FStar_Util.bind_opt _146_841 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _146_853 = (let _146_852 = (let _146_851 = (name_not_found l)
in ((_146_851), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_146_852))
in (Prims.raise _146_853))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_1065 -> (match (_52_1065) with
| (m1, m2, _52_1060, _52_1062, _52_1064) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _146_929 = (let _146_928 = (let _146_927 = (let _146_926 = (FStar_Syntax_Print.lid_to_string l1)
in (let _146_925 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _146_926 _146_925)))
in ((_146_927), (env.range)))
in FStar_Syntax_Syntax.Error (_146_928))
in (Prims.raise _146_929))
end
| Some (_52_1068, _52_1070, m3, j1, j2) -> begin
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
(let _146_944 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _146_944))
end
| Some (md) -> begin
(

let _52_1091 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_52_1091) with
| (_52_1089, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_1100))::((wp, _52_1096))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _52_1108 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_1115) -> begin
(

let effects = (

let _52_1118 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1118.order; joins = _52_1118.joins})
in (

let _52_1121 = env
in {solver = _52_1121.solver; range = _52_1121.range; curmodule = _52_1121.curmodule; gamma = _52_1121.gamma; gamma_cache = _52_1121.gamma_cache; modules = _52_1121.modules; expected_typ = _52_1121.expected_typ; sigtab = _52_1121.sigtab; is_pattern = _52_1121.is_pattern; instantiate_imp = _52_1121.instantiate_imp; effects = effects; generalize = _52_1121.generalize; letrecs = _52_1121.letrecs; top_level = _52_1121.top_level; check_uvars = _52_1121.check_uvars; use_eq = _52_1121.use_eq; is_iface = _52_1121.is_iface; admit = _52_1121.admit; lax = _52_1121.lax; lax_universes = _52_1121.lax_universes; type_of = _52_1121.type_of; universe_of = _52_1121.universe_of; use_bv_sorts = _52_1121.use_bv_sorts; qname_and_index = _52_1121.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1125) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _146_959 = (e1.mlift r wp1)
in (e2.mlift r _146_959)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1140 = (inst_tscheme lift_t)
in (match (_52_1140) with
| (_52_1138, lift_t) -> begin
(let _146_971 = (let _146_970 = (let _146_969 = (let _146_968 = (FStar_Syntax_Syntax.as_arg r)
in (let _146_967 = (let _146_966 = (FStar_Syntax_Syntax.as_arg wp1)
in (_146_966)::[])
in (_146_968)::_146_967))
in ((lift_t), (_146_969)))
in FStar_Syntax_Syntax.Tm_app (_146_970))
in (FStar_Syntax_Syntax.mk _146_971 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift_wp)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _146_988 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _146_988 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _146_989 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _146_989 FStar_Syntax_Syntax.Delta_constant None))
in (let _146_990 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _146_990)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1157 -> (match (_52_1157) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _146_996 -> Some (_146_996)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _146_1004 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _146_1003 = (find_edge order ((i), (k)))
in (let _146_1002 = (find_edge order ((k), (j)))
in ((_146_1003), (_146_1002))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1169 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _146_1004))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let _52_1175 = (FStar_All.pipe_right order (FStar_List.iter (fun edge -> if ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (let _146_1008 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right _146_1008 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))) then begin
(let _146_1012 = (let _146_1011 = (let _146_1010 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (let _146_1009 = (get_range env)
in ((_146_1010), (_146_1009))))
in FStar_Syntax_Syntax.Error (_146_1011))
in (Prims.raise _146_1012))
end else begin
()
end)))
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _146_1102 = (find_edge order ((i), (k)))
in (let _146_1101 = (find_edge order ((j), (k)))
in ((_146_1102), (_146_1101))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _52_1189, _52_1191) -> begin
if ((let _146_1103 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _146_1103)) && (not ((let _146_1104 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _146_1104))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _52_1195 -> begin
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

let _52_1204 = env.effects
in {decls = _52_1204.decls; order = order; joins = joins})
in (

let _52_1207 = env
in {solver = _52_1207.solver; range = _52_1207.range; curmodule = _52_1207.curmodule; gamma = _52_1207.gamma; gamma_cache = _52_1207.gamma_cache; modules = _52_1207.modules; expected_typ = _52_1207.expected_typ; sigtab = _52_1207.sigtab; is_pattern = _52_1207.is_pattern; instantiate_imp = _52_1207.instantiate_imp; effects = effects; generalize = _52_1207.generalize; letrecs = _52_1207.letrecs; top_level = _52_1207.top_level; check_uvars = _52_1207.check_uvars; use_eq = _52_1207.use_eq; is_iface = _52_1207.is_iface; admit = _52_1207.admit; lax = _52_1207.lax; lax_universes = _52_1207.lax_universes; type_of = _52_1207.type_of; universe_of = _52_1207.universe_of; use_bv_sorts = _52_1207.use_bv_sorts; qname_and_index = _52_1207.qname_and_index}))))))))))))))
end
| _52_1210 -> begin
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
(let _146_1153 = (push x rest)
in (local)::_146_1153)
end))
in (

let _52_1232 = env
in (let _146_1154 = (push s env.gamma)
in {solver = _52_1232.solver; range = _52_1232.range; curmodule = _52_1232.curmodule; gamma = _146_1154; gamma_cache = _52_1232.gamma_cache; modules = _52_1232.modules; expected_typ = _52_1232.expected_typ; sigtab = _52_1232.sigtab; is_pattern = _52_1232.is_pattern; instantiate_imp = _52_1232.instantiate_imp; effects = _52_1232.effects; generalize = _52_1232.generalize; letrecs = _52_1232.letrecs; top_level = _52_1232.top_level; check_uvars = _52_1232.check_uvars; use_eq = _52_1232.use_eq; is_iface = _52_1232.is_iface; admit = _52_1232.admit; lax = _52_1232.lax; lax_universes = _52_1232.lax_universes; type_of = _52_1232.type_of; universe_of = _52_1232.universe_of; use_bv_sorts = _52_1232.use_bv_sorts; qname_and_index = _52_1232.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (let _146_1161 = (let _146_1160 = (let _146_1159 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_146_1159), (s)))
in Binding_sig (_146_1160))
in (push_in_gamma env _146_1161))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (let _146_1170 = (let _146_1169 = (let _146_1168 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_146_1168), (s), (us)))
in Binding_sig_inst (_146_1169))
in (push_in_gamma env _146_1170))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1243 = env
in {solver = _52_1243.solver; range = _52_1243.range; curmodule = _52_1243.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1243.gamma_cache; modules = _52_1243.modules; expected_typ = _52_1243.expected_typ; sigtab = _52_1243.sigtab; is_pattern = _52_1243.is_pattern; instantiate_imp = _52_1243.instantiate_imp; effects = _52_1243.effects; generalize = _52_1243.generalize; letrecs = _52_1243.letrecs; top_level = _52_1243.top_level; check_uvars = _52_1243.check_uvars; use_eq = _52_1243.use_eq; is_iface = _52_1243.is_iface; admit = _52_1243.admit; lax = _52_1243.lax; lax_universes = _52_1243.lax_universes; type_of = _52_1243.type_of; universe_of = _52_1243.universe_of; use_bv_sorts = _52_1243.use_bv_sorts; qname_and_index = _52_1243.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1253 -> (match (_52_1253) with
| (x, _52_1252) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1258 = ()
in (

let x = (

let _52_1260 = x
in {FStar_Syntax_Syntax.ppname = _52_1260.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1260.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1270 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1272 = env
in {solver = _52_1272.solver; range = _52_1272.range; curmodule = _52_1272.curmodule; gamma = []; gamma_cache = _52_1272.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1272.sigtab; is_pattern = _52_1272.is_pattern; instantiate_imp = _52_1272.instantiate_imp; effects = _52_1272.effects; generalize = _52_1272.generalize; letrecs = _52_1272.letrecs; top_level = _52_1272.top_level; check_uvars = _52_1272.check_uvars; use_eq = _52_1272.use_eq; is_iface = _52_1272.is_iface; admit = _52_1272.admit; lax = _52_1272.lax; lax_universes = _52_1272.lax_universes; type_of = _52_1272.type_of; universe_of = _52_1272.universe_of; use_bv_sorts = _52_1272.use_bv_sorts; qname_and_index = _52_1272.qname_and_index})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1280 = env
in {solver = _52_1280.solver; range = _52_1280.range; curmodule = _52_1280.curmodule; gamma = _52_1280.gamma; gamma_cache = _52_1280.gamma_cache; modules = _52_1280.modules; expected_typ = Some (t); sigtab = _52_1280.sigtab; is_pattern = _52_1280.is_pattern; instantiate_imp = _52_1280.instantiate_imp; effects = _52_1280.effects; generalize = _52_1280.generalize; letrecs = _52_1280.letrecs; top_level = _52_1280.top_level; check_uvars = _52_1280.check_uvars; use_eq = false; is_iface = _52_1280.is_iface; admit = _52_1280.admit; lax = _52_1280.lax; lax_universes = _52_1280.lax_universes; type_of = _52_1280.type_of; universe_of = _52_1280.universe_of; use_bv_sorts = _52_1280.use_bv_sorts; qname_and_index = _52_1280.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _146_1213 = (expected_typ env)
in (((

let _52_1287 = env
in {solver = _52_1287.solver; range = _52_1287.range; curmodule = _52_1287.curmodule; gamma = _52_1287.gamma; gamma_cache = _52_1287.gamma_cache; modules = _52_1287.modules; expected_typ = None; sigtab = _52_1287.sigtab; is_pattern = _52_1287.is_pattern; instantiate_imp = _52_1287.instantiate_imp; effects = _52_1287.effects; generalize = _52_1287.generalize; letrecs = _52_1287.letrecs; top_level = _52_1287.top_level; check_uvars = _52_1287.check_uvars; use_eq = false; is_iface = _52_1287.is_iface; admit = _52_1287.admit; lax = _52_1287.lax; lax_universes = _52_1287.lax_universes; type_of = _52_1287.type_of; universe_of = _52_1287.universe_of; use_bv_sorts = _52_1287.use_bv_sorts; qname_and_index = _52_1287.qname_and_index})), (_146_1213))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _146_1219 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1294, se) -> begin
(se)::[]
end
| _52_1299 -> begin
[]
end))))
in (FStar_All.pipe_right _146_1219 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1301 = (add_sigelts env sigs)
in (

let _52_1303 = env
in {solver = _52_1303.solver; range = _52_1303.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1303.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1303.expected_typ; sigtab = _52_1303.sigtab; is_pattern = _52_1303.is_pattern; instantiate_imp = _52_1303.instantiate_imp; effects = _52_1303.effects; generalize = _52_1303.generalize; letrecs = _52_1303.letrecs; top_level = _52_1303.top_level; check_uvars = _52_1303.check_uvars; use_eq = _52_1303.use_eq; is_iface = _52_1303.is_iface; admit = _52_1303.admit; lax = _52_1303.lax; lax_universes = _52_1303.lax_universes; type_of = _52_1303.type_of; universe_of = _52_1303.universe_of; use_bv_sorts = _52_1303.use_bv_sorts; qname_and_index = _52_1303.qname_and_index})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1316))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _146_1231 = (let _146_1230 = (FStar_Syntax_Free.uvars t)
in (ext out _146_1230))
in (aux _146_1231 tl))
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
(let _146_1243 = (let _146_1242 = (FStar_Syntax_Free.univs t)
in (ext out _146_1242))
in (aux _146_1243 tl))
end
| (Binding_sig (_52_1386))::_52_1384 -> begin
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


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _146_1250 = (let _146_1249 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _146_1249 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _146_1250 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1418) -> begin
(FStar_List.append lids keys)
end
| _52_1422 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1424 v keys -> (let _146_1273 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _146_1273 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1428 -> ()); push = (fun _52_1430 -> ()); pop = (fun _52_1432 -> ()); mark = (fun _52_1434 -> ()); reset_mark = (fun _52_1436 -> ()); commit_mark = (fun _52_1438 -> ()); encode_modul = (fun _52_1440 _52_1442 -> ()); encode_sig = (fun _52_1444 _52_1446 -> ()); solve = (fun _52_1448 _52_1450 _52_1452 -> ()); is_trivial = (fun _52_1454 _52_1456 -> false); finish = (fun _52_1458 -> ()); refresh = (fun _52_1459 -> ())}




