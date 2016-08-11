
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) Prims.option} 
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
| _52_103 -> begin
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
| (FStar_Syntax_Syntax.Delta_abstract (l1), _52_152) -> begin
(aux l1 l2)
end
| (_52_155, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _144_395 = (aux l1 l2)
in Unfold (_144_395)))
end))


let default_table_size : Prims.int = 200


let new_sigtab = (fun _52_159 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _52_160 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _144_427 = (new_gamma_cache ())
in (let _144_426 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _144_427; modules = []; expected_typ = None; sigtab = _144_426; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env; es_incr_query_index : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let query_indices = (FStar_Util.mk_ref (([])::[]))
in (

let push_query_indices = (fun _52_176 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| [] -> begin
(FStar_All.failwith "Empty query indices!")
end
| _52_179 -> begin
(let _144_492 = (let _144_491 = (let _144_489 = (FStar_ST.read query_indices)
in (FStar_List.hd _144_489))
in (let _144_490 = (FStar_ST.read query_indices)
in (_144_491)::_144_490))
in (FStar_ST.op_Colon_Equals query_indices _144_492))
end)
end))
in (

let pop_query_indices = (fun _52_181 -> (match (()) with
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

let add_query_index = (fun _52_189 -> (match (_52_189) with
| (l, n) -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n)))::hd)::tl))
end
| _52_194 -> begin
(FStar_All.failwith "Empty query indices")
end)
end))
in (

let peek_query_indices = (fun _52_196 -> (match (()) with
| () -> begin
(let _144_499 = (FStar_ST.read query_indices)
in (FStar_List.hd _144_499))
end))
in (

let commit_query_index_mark = (fun _52_198 -> (match (()) with
| () -> begin
(match ((FStar_ST.read query_indices)) with
| (hd)::(_52_201)::tl -> begin
(FStar_ST.op_Colon_Equals query_indices ((hd)::tl))
end
| _52_206 -> begin
(FStar_All.failwith "Unmarked query index stack")
end)
end))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push_stack = (fun env -> (

let _52_210 = (let _144_505 = (let _144_504 = (FStar_ST.read stack)
in (env)::_144_504)
in (FStar_ST.op_Colon_Equals stack _144_505))
in (

let _52_212 = env
in (let _144_507 = (FStar_Util.smap_copy (gamma_cache env))
in (let _144_506 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_212.solver; range = _52_212.range; curmodule = _52_212.curmodule; gamma = _52_212.gamma; gamma_cache = _144_507; modules = _52_212.modules; expected_typ = _52_212.expected_typ; sigtab = _144_506; is_pattern = _52_212.is_pattern; instantiate_imp = _52_212.instantiate_imp; effects = _52_212.effects; generalize = _52_212.generalize; letrecs = _52_212.letrecs; top_level = _52_212.top_level; check_uvars = _52_212.check_uvars; use_eq = _52_212.use_eq; is_iface = _52_212.is_iface; admit = _52_212.admit; lax = _52_212.lax; type_of = _52_212.type_of; universe_of = _52_212.universe_of; use_bv_sorts = _52_212.use_bv_sorts; qname_and_index = _52_212.qname_and_index})))))
in (

let pop_stack = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_219 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_222 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let push = (fun env -> (

let _52_225 = (push_query_indices ())
in (push_stack env)))
in (

let pop = (fun env -> (

let _52_229 = (pop_query_indices ())
in (pop_stack env)))
in (

let mark = (fun env -> (

let _52_233 = (push_query_indices ())
in (push_stack env)))
in (

let commit_mark = (fun env -> (

let _52_237 = (commit_query_index_mark ())
in (

let _52_239 = (let _144_518 = (pop_stack env)
in (Prims.ignore _144_518))
in env)))
in (

let reset_mark = (fun env -> (

let _52_243 = (pop_query_indices ())
in (pop_stack env)))
in (

let incr_query_index = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(match ((FStar_All.pipe_right qix (FStar_List.tryFind (fun _52_256 -> (match (_52_256) with
| (m, _52_255) -> begin
(FStar_Ident.lid_equals l m)
end))))) with
| None -> begin
(

let next = (n + 1)
in (

let _52_259 = (add_query_index ((l), (next)))
in (

let _52_261 = env
in {solver = _52_261.solver; range = _52_261.range; curmodule = _52_261.curmodule; gamma = _52_261.gamma; gamma_cache = _52_261.gamma_cache; modules = _52_261.modules; expected_typ = _52_261.expected_typ; sigtab = _52_261.sigtab; is_pattern = _52_261.is_pattern; instantiate_imp = _52_261.instantiate_imp; effects = _52_261.effects; generalize = _52_261.generalize; letrecs = _52_261.letrecs; top_level = _52_261.top_level; check_uvars = _52_261.check_uvars; use_eq = _52_261.use_eq; is_iface = _52_261.is_iface; admit = _52_261.admit; lax = _52_261.lax; type_of = _52_261.type_of; universe_of = _52_261.universe_of; use_bv_sorts = _52_261.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end
| Some (_52_264, m) -> begin
(

let next = (m + 1)
in (

let _52_269 = (add_query_index ((l), (next)))
in (

let _52_271 = env
in {solver = _52_271.solver; range = _52_271.range; curmodule = _52_271.curmodule; gamma = _52_271.gamma; gamma_cache = _52_271.gamma_cache; modules = _52_271.modules; expected_typ = _52_271.expected_typ; sigtab = _52_271.sigtab; is_pattern = _52_271.is_pattern; instantiate_imp = _52_271.instantiate_imp; effects = _52_271.effects; generalize = _52_271.generalize; letrecs = _52_271.letrecs; top_level = _52_271.top_level; check_uvars = _52_271.check_uvars; use_eq = _52_271.use_eq; is_iface = _52_271.is_iface; admit = _52_271.admit; lax = _52_271.lax; type_of = _52_271.type_of; universe_of = _52_271.universe_of; use_bv_sorts = _52_271.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end)
end)))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop; es_incr_query_index = incr_query_index})))))))))))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_275 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_278 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_281 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_284 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_288 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let incr_query_index : env  ->  env = (fun env -> (stack_ops.es_incr_query_index env))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_295 = e
in {solver = _52_295.solver; range = r; curmodule = _52_295.curmodule; gamma = _52_295.gamma; gamma_cache = _52_295.gamma_cache; modules = _52_295.modules; expected_typ = _52_295.expected_typ; sigtab = _52_295.sigtab; is_pattern = _52_295.is_pattern; instantiate_imp = _52_295.instantiate_imp; effects = _52_295.effects; generalize = _52_295.generalize; letrecs = _52_295.letrecs; top_level = _52_295.top_level; check_uvars = _52_295.check_uvars; use_eq = _52_295.use_eq; is_iface = _52_295.is_iface; admit = _52_295.admit; lax = _52_295.lax; type_of = _52_295.type_of; universe_of = _52_295.universe_of; use_bv_sorts = _52_295.use_bv_sorts; qname_and_index = _52_295.qname_and_index})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_302 = env
in {solver = _52_302.solver; range = _52_302.range; curmodule = lid; gamma = _52_302.gamma; gamma_cache = _52_302.gamma_cache; modules = _52_302.modules; expected_typ = _52_302.expected_typ; sigtab = _52_302.sigtab; is_pattern = _52_302.is_pattern; instantiate_imp = _52_302.instantiate_imp; effects = _52_302.effects; generalize = _52_302.generalize; letrecs = _52_302.letrecs; top_level = _52_302.top_level; check_uvars = _52_302.check_uvars; use_eq = _52_302.use_eq; is_iface = _52_302.is_iface; admit = _52_302.admit; lax = _52_302.lax; type_of = _52_302.type_of; universe_of = _52_302.universe_of; use_bv_sorts = _52_302.use_bv_sorts; qname_and_index = _52_302.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _144_571 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _144_571)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _52_311 -> (match (()) with
| () -> begin
(let _144_574 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_144_574))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _52_323) -> begin
(

let _52_325 = ()
in (

let n = ((FStar_List.length formals) - 1)
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _144_581 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_144_581))))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_338 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_346 -> (match (_52_346) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_349 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _144_597 = (let _144_596 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _144_595 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _144_594 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _144_593 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _144_596 _144_595 _144_594 _144_593)))))
in (FStar_All.failwith _144_597))
end else begin
()
end
in (let _144_598 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _144_598))))
end
| _52_352 -> begin
(let _144_600 = (let _144_599 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _144_599))
in (FStar_All.failwith _144_600))
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
| ([], _52_363) -> begin
Maybe
end
| (_52_366, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_377 -> begin
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

let _52_383 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _144_620 = (let _144_619 = (inst_tscheme t)
in FStar_Util.Inl (_144_619))
in Some (_144_620))
end else begin
None
end
end
| Binding_sig (_52_392, FStar_Syntax_Syntax.Sig_bundle (ses, _52_395, _52_397, _52_399)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _144_622 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _144_622 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr (((se), (None)))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_412) -> begin
Some (t)
end
| _52_415 -> begin
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
| _52_422 -> begin
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
| Some (_52_432) -> begin
true
end))


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


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_4 -> (match (_52_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_475 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_479, (lb)::[]), _52_484, _52_486, _52_488) -> begin
(let _144_656 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_144_656))
end
| FStar_Syntax_Syntax.Sig_let ((_52_492, lbs), _52_496, _52_498, _52_500) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_505) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _144_658 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_144_658))
end else begin
None
end
end)))
end
| _52_510 -> begin
None
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _144_666 = (let _144_665 = (let _144_664 = (variable_not_found bv)
in (let _144_663 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_144_664), (_144_663))))
in FStar_Syntax_Syntax.Error (_144_665))
in (Prims.raise _144_666))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_519) -> begin
(let _144_672 = (let _144_671 = (let _144_670 = (let _144_669 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _144_669))
in ((ne.FStar_Syntax_Syntax.univs), (_144_670)))
in (inst_tscheme _144_671))
in Some (_144_672))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_526, _52_528, _52_530) -> begin
(let _144_676 = (let _144_675 = (let _144_674 = (let _144_673 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _144_673))
in ((us), (_144_674)))
in (inst_tscheme _144_675))
in Some (_144_676))
end
| _52_534 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_544, t) -> begin
Some (t)
end)
end
| _52_549 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (

let mapper = (fun _52_5 -> (match (_52_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_556, uvs, t, _52_560, _52_562, _52_564, _52_566, _52_568), None) -> begin
(let _144_687 = (inst_tscheme ((uvs), (t)))
in Some (_144_687))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_579), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _144_688 = (inst_tscheme ((uvs), (t)))
in Some (_144_688))
end else begin
None
end
end else begin
(let _144_689 = (inst_tscheme ((uvs), (t)))
in Some (_144_689))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_590, _52_592, _52_594, _52_596), None) -> begin
(match (tps) with
| [] -> begin
(let _144_691 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _144_690 -> Some (_144_690)) _144_691))
end
| _52_604 -> begin
(let _144_696 = (let _144_695 = (let _144_694 = (let _144_693 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _144_693))
in ((uvs), (_144_694)))
in (inst_tscheme _144_695))
in (FStar_All.pipe_left (fun _144_692 -> Some (_144_692)) _144_696))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_610, _52_612, _52_614, _52_616), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _144_698 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _144_697 -> Some (_144_697)) _144_698))
end
| _52_625 -> begin
(let _144_703 = (let _144_702 = (let _144_701 = (let _144_700 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _144_700))
in ((uvs), (_144_701)))
in (inst_tscheme_with _144_702 us))
in (FStar_All.pipe_left (fun _144_699 -> Some (_144_699)) _144_703))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_629), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_634 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _144_704 = (lookup_qname env lid)
in (FStar_Util.bind_opt _144_704 mapper))) with
| Some (us, t) -> begin
Some (((us), ((

let _52_640 = t
in {FStar_Syntax_Syntax.n = _52_640.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_640.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_640.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_6 -> (match (_52_6) with
| FStar_Util.Inl (_52_647) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_651) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_655, _52_657, _52_659, qs, _52_662) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_666) -> begin
Some (true)
end
| _52_669 -> begin
Some (false)
end)
end))
in (match ((let _144_711 = (lookup_qname env lid)
in (FStar_Util.bind_opt _144_711 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _144_718 = (let _144_717 = (let _144_716 = (name_not_found l)
in ((_144_716), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_144_717))
in (Prims.raise _144_718))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_682, uvs, t, _52_686, _52_688), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_696 -> begin
(let _144_725 = (let _144_724 = (let _144_723 = (name_not_found lid)
in ((_144_723), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_144_724))
in (Prims.raise _144_725))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_700, uvs, t, _52_704, _52_706, _52_708, _52_710, _52_712), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_720 -> begin
(let _144_732 = (let _144_731 = (let _144_730 = (name_not_found lid)
in ((_144_730), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_144_731))
in (Prims.raise _144_732))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_730, lbs), _52_734, _52_736, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _144_741 = (let _144_740 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in ((lb.FStar_Syntax_Syntax.lbunivs), (_144_740)))
in Some (_144_741))
end else begin
None
end)))
end
| _52_743 -> begin
None
end)
end
| _52_745 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _144_748 = (let _144_747 = (let _144_746 = (name_not_found ftv)
in ((_144_746), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_144_747))
in (Prims.raise _144_748))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_755 -> (match (()) with
| () -> begin
(let _144_759 = (let _144_758 = (FStar_Util.string_of_int i)
in (let _144_757 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _144_758 _144_757)))
in (FStar_All.failwith _144_759))
end))
in (

let _52_759 = (lookup_datacon env lid)
in (match (_52_759) with
| (_52_757, t) -> begin
(match ((let _144_760 = (FStar_Syntax_Subst.compress t)
in _144_760.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_762) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _144_761 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _144_761 Prims.fst)))
end
end
| _52_767 -> begin
(fail ())
end)
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_771, uvs, t, q, _52_776), None)) -> begin
Some (((((uvs), (t))), (q)))
end
| _52_784 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_794), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_804 -> begin
false
end)))) then begin
None
end else begin
(

let insts = if (FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) then begin
(univ)::(FStar_Syntax_Syntax.U_zero)::[]
end else begin
(univ)::[]
end
in (match (((binders), (univs))) with
| ([], _52_808) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_811, (_52_818)::(_52_815)::_52_813) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _144_775 = (let _144_774 = (FStar_Syntax_Print.lid_to_string lid)
in (let _144_773 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _144_774 _144_773)))
in (FStar_All.failwith _144_775))
end
| _52_822 -> begin
(

let _52_826 = (let _144_777 = (let _144_776 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_144_776)))
in (inst_tscheme_with _144_777 insts))
in (match (_52_826) with
| (_52_824, t) -> begin
(match ((let _144_778 = (FStar_Syntax_Subst.compress t)
in _144_778.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| _52_832 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_834 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create 20)
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_842, c) -> begin
(

let l = (FStar_Syntax_Util.comp_to_comp_typ c).FStar_Syntax_Syntax.effect_name
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

let _52_856 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_862, _52_864, _52_866, _52_868, _52_870, dcs, _52_873, _52_875), _52_879)) -> begin
dcs
end
| _52_884 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_888, _52_890, _52_892, l, _52_895, _52_897, _52_899, _52_901), _52_905)) -> begin
l
end
| _52_910 -> begin
(let _144_794 = (let _144_793 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _144_793))
in (FStar_All.failwith _144_794))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_914, _52_916, _52_918, _52_920, _52_922, _52_924, _52_926, _52_928), _52_932)) -> begin
true
end
| _52_937 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_941, _52_943, _52_945, _52_947, _52_949, _52_951, tags, _52_954), _52_958)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_970 -> begin
false
end)) tags)
end
| _52_972 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_976, _52_978, _52_980, quals, _52_983), _52_987)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_993) -> begin
true
end
| _52_996 -> begin
false
end)) quals)
end
| _52_998 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _144_813 = (FStar_Syntax_Util.un_uinst head)
in _144_813.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_1004 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _144_825 = (let _144_824 = (let _144_823 = (name_not_found l)
in ((_144_823), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_144_824))
in (Prims.raise _144_825))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_1032 -> (match (_52_1032) with
| (m1, m2, _52_1027, _52_1029, _52_1031) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _144_901 = (let _144_900 = (let _144_899 = (let _144_898 = (FStar_Syntax_Print.lid_to_string l1)
in (let _144_897 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _144_898 _144_897)))
in ((_144_899), (env.range)))
in FStar_Syntax_Syntax.Error (_144_900))
in (Prims.raise _144_901))
end
| Some (_52_1035, _52_1037, m3, j1, j2) -> begin
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
(let _144_916 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _144_916))
end
| Some (md) -> begin
(

let _52_1058 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_52_1058) with
| (_52_1056, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_1067))::((wp, _52_1063))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _52_1075 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_1082) -> begin
(

let effects = (

let _52_1085 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1085.order; joins = _52_1085.joins})
in (

let _52_1088 = env
in {solver = _52_1088.solver; range = _52_1088.range; curmodule = _52_1088.curmodule; gamma = _52_1088.gamma; gamma_cache = _52_1088.gamma_cache; modules = _52_1088.modules; expected_typ = _52_1088.expected_typ; sigtab = _52_1088.sigtab; is_pattern = _52_1088.is_pattern; instantiate_imp = _52_1088.instantiate_imp; effects = effects; generalize = _52_1088.generalize; letrecs = _52_1088.letrecs; top_level = _52_1088.top_level; check_uvars = _52_1088.check_uvars; use_eq = _52_1088.use_eq; is_iface = _52_1088.is_iface; admit = _52_1088.admit; lax = _52_1088.lax; type_of = _52_1088.type_of; universe_of = _52_1088.universe_of; use_bv_sorts = _52_1088.use_bv_sorts; qname_and_index = _52_1088.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1092) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _144_931 = (e1.mlift r wp1)
in (e2.mlift r _144_931)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1107 = (inst_tscheme lift_t)
in (match (_52_1107) with
| (_52_1105, lift_t) -> begin
(let _144_943 = (let _144_942 = (let _144_941 = (let _144_940 = (FStar_Syntax_Syntax.as_arg r)
in (let _144_939 = (let _144_938 = (FStar_Syntax_Syntax.as_arg wp1)
in (_144_938)::[])
in (_144_940)::_144_939))
in ((lift_t), (_144_941)))
in FStar_Syntax_Syntax.Tm_app (_144_942))
in (FStar_Syntax_Syntax.mk _144_943 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift_wp)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _144_960 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _144_960 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _144_961 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _144_961 FStar_Syntax_Syntax.Delta_constant None))
in (let _144_962 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _144_962)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1124 -> (match (_52_1124) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _144_968 -> Some (_144_968)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _144_976 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _144_975 = (find_edge order ((i), (k)))
in (let _144_974 = (find_edge order ((k), (j)))
in ((_144_975), (_144_974))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1136 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _144_976))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _144_1068 = (find_edge order ((i), (k)))
in (let _144_1067 = (find_edge order ((j), (k)))
in ((_144_1068), (_144_1067))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _52_1153, _52_1155) -> begin
if ((let _144_1069 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _144_1069)) && (not ((let _144_1070 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _144_1070))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _52_1159 -> begin
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

let _52_1168 = env.effects
in {decls = _52_1168.decls; order = order; joins = joins})
in (

let _52_1171 = env
in {solver = _52_1171.solver; range = _52_1171.range; curmodule = _52_1171.curmodule; gamma = _52_1171.gamma; gamma_cache = _52_1171.gamma_cache; modules = _52_1171.modules; expected_typ = _52_1171.expected_typ; sigtab = _52_1171.sigtab; is_pattern = _52_1171.is_pattern; instantiate_imp = _52_1171.instantiate_imp; effects = effects; generalize = _52_1171.generalize; letrecs = _52_1171.letrecs; top_level = _52_1171.top_level; check_uvars = _52_1171.check_uvars; use_eq = _52_1171.use_eq; is_iface = _52_1171.is_iface; admit = _52_1171.admit; lax = _52_1171.lax; type_of = _52_1171.type_of; universe_of = _52_1171.universe_of; use_bv_sorts = _52_1171.use_bv_sorts; qname_and_index = _52_1171.qname_and_index})))))))))))))
end
| _52_1174 -> begin
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
(let _144_1119 = (push x rest)
in (local)::_144_1119)
end))
in (

let _52_1196 = env
in (let _144_1120 = (push s env.gamma)
in {solver = _52_1196.solver; range = _52_1196.range; curmodule = _52_1196.curmodule; gamma = _144_1120; gamma_cache = _52_1196.gamma_cache; modules = _52_1196.modules; expected_typ = _52_1196.expected_typ; sigtab = _52_1196.sigtab; is_pattern = _52_1196.is_pattern; instantiate_imp = _52_1196.instantiate_imp; effects = _52_1196.effects; generalize = _52_1196.generalize; letrecs = _52_1196.letrecs; top_level = _52_1196.top_level; check_uvars = _52_1196.check_uvars; use_eq = _52_1196.use_eq; is_iface = _52_1196.is_iface; admit = _52_1196.admit; lax = _52_1196.lax; type_of = _52_1196.type_of; universe_of = _52_1196.universe_of; use_bv_sorts = _52_1196.use_bv_sorts; qname_and_index = _52_1196.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (let _144_1127 = (let _144_1126 = (let _144_1125 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_144_1125), (s)))
in Binding_sig (_144_1126))
in (push_in_gamma env _144_1127))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (let _144_1136 = (let _144_1135 = (let _144_1134 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_144_1134), (s), (us)))
in Binding_sig_inst (_144_1135))
in (push_in_gamma env _144_1136))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1207 = env
in {solver = _52_1207.solver; range = _52_1207.range; curmodule = _52_1207.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1207.gamma_cache; modules = _52_1207.modules; expected_typ = _52_1207.expected_typ; sigtab = _52_1207.sigtab; is_pattern = _52_1207.is_pattern; instantiate_imp = _52_1207.instantiate_imp; effects = _52_1207.effects; generalize = _52_1207.generalize; letrecs = _52_1207.letrecs; top_level = _52_1207.top_level; check_uvars = _52_1207.check_uvars; use_eq = _52_1207.use_eq; is_iface = _52_1207.is_iface; admit = _52_1207.admit; lax = _52_1207.lax; type_of = _52_1207.type_of; universe_of = _52_1207.universe_of; use_bv_sorts = _52_1207.use_bv_sorts; qname_and_index = _52_1207.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1217 -> (match (_52_1217) with
| (x, _52_1216) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1222 = ()
in (

let x = (

let _52_1224 = x
in {FStar_Syntax_Syntax.ppname = _52_1224.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1224.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1234 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1236 = env
in {solver = _52_1236.solver; range = _52_1236.range; curmodule = _52_1236.curmodule; gamma = []; gamma_cache = _52_1236.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1236.sigtab; is_pattern = _52_1236.is_pattern; instantiate_imp = _52_1236.instantiate_imp; effects = _52_1236.effects; generalize = _52_1236.generalize; letrecs = _52_1236.letrecs; top_level = _52_1236.top_level; check_uvars = _52_1236.check_uvars; use_eq = _52_1236.use_eq; is_iface = _52_1236.is_iface; admit = _52_1236.admit; lax = _52_1236.lax; type_of = _52_1236.type_of; universe_of = _52_1236.universe_of; use_bv_sorts = _52_1236.use_bv_sorts; qname_and_index = _52_1236.qname_and_index})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1244 = env
in {solver = _52_1244.solver; range = _52_1244.range; curmodule = _52_1244.curmodule; gamma = _52_1244.gamma; gamma_cache = _52_1244.gamma_cache; modules = _52_1244.modules; expected_typ = Some (t); sigtab = _52_1244.sigtab; is_pattern = _52_1244.is_pattern; instantiate_imp = _52_1244.instantiate_imp; effects = _52_1244.effects; generalize = _52_1244.generalize; letrecs = _52_1244.letrecs; top_level = _52_1244.top_level; check_uvars = _52_1244.check_uvars; use_eq = false; is_iface = _52_1244.is_iface; admit = _52_1244.admit; lax = _52_1244.lax; type_of = _52_1244.type_of; universe_of = _52_1244.universe_of; use_bv_sorts = _52_1244.use_bv_sorts; qname_and_index = _52_1244.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _144_1179 = (expected_typ env)
in (((

let _52_1251 = env
in {solver = _52_1251.solver; range = _52_1251.range; curmodule = _52_1251.curmodule; gamma = _52_1251.gamma; gamma_cache = _52_1251.gamma_cache; modules = _52_1251.modules; expected_typ = None; sigtab = _52_1251.sigtab; is_pattern = _52_1251.is_pattern; instantiate_imp = _52_1251.instantiate_imp; effects = _52_1251.effects; generalize = _52_1251.generalize; letrecs = _52_1251.letrecs; top_level = _52_1251.top_level; check_uvars = _52_1251.check_uvars; use_eq = false; is_iface = _52_1251.is_iface; admit = _52_1251.admit; lax = _52_1251.lax; type_of = _52_1251.type_of; universe_of = _52_1251.universe_of; use_bv_sorts = _52_1251.use_bv_sorts; qname_and_index = _52_1251.qname_and_index})), (_144_1179))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _144_1185 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1258, se) -> begin
(se)::[]
end
| _52_1263 -> begin
[]
end))))
in (FStar_All.pipe_right _144_1185 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1265 = (add_sigelts env sigs)
in (

let _52_1267 = env
in {solver = _52_1267.solver; range = _52_1267.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1267.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1267.expected_typ; sigtab = _52_1267.sigtab; is_pattern = _52_1267.is_pattern; instantiate_imp = _52_1267.instantiate_imp; effects = _52_1267.effects; generalize = _52_1267.generalize; letrecs = _52_1267.letrecs; top_level = _52_1267.top_level; check_uvars = _52_1267.check_uvars; use_eq = _52_1267.use_eq; is_iface = _52_1267.is_iface; admit = _52_1267.admit; lax = _52_1267.lax; type_of = _52_1267.type_of; universe_of = _52_1267.universe_of; use_bv_sorts = _52_1267.use_bv_sorts; qname_and_index = _52_1267.qname_and_index})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1280))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _144_1197 = (let _144_1196 = (FStar_Syntax_Free.uvars t)
in (ext out _144_1196))
in (aux _144_1197 tl))
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
(let _144_1209 = (let _144_1208 = (FStar_Syntax_Free.univs t)
in (ext out _144_1208))
in (aux _144_1209 tl))
end
| (Binding_sig (_52_1350))::_52_1348 -> begin
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


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _144_1216 = (let _144_1215 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _144_1215 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _144_1216 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1382) -> begin
(FStar_List.append lids keys)
end
| _52_1386 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1388 v keys -> (let _144_1239 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _144_1239 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1392 -> ()); push = (fun _52_1394 -> ()); pop = (fun _52_1396 -> ()); mark = (fun _52_1398 -> ()); reset_mark = (fun _52_1400 -> ()); commit_mark = (fun _52_1402 -> ()); encode_modul = (fun _52_1404 _52_1406 -> ()); encode_sig = (fun _52_1408 _52_1410 -> ()); solve = (fun _52_1412 _52_1414 _52_1416 -> ()); is_trivial = (fun _52_1418 _52_1420 -> false); finish = (fun _52_1422 -> ()); refresh = (fun _52_1423 -> ())}




