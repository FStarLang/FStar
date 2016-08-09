
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
| (_52_185)::tl -> begin
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
(let _144_499 = (FStar_ST.read query_indices)
in (FStar_List.hd _144_499))
end))
in (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _52_201 = (push_query_indices ())
in (

let _52_203 = (let _144_503 = (let _144_502 = (FStar_ST.read stack)
in (env)::_144_502)
in (FStar_ST.op_Colon_Equals stack _144_503))
in (

let _52_205 = env
in (let _144_505 = (FStar_Util.smap_copy (gamma_cache env))
in (let _144_504 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_205.solver; range = _52_205.range; curmodule = _52_205.curmodule; gamma = _52_205.gamma; gamma_cache = _144_505; modules = _52_205.modules; expected_typ = _52_205.expected_typ; sigtab = _144_504; is_pattern = _52_205.is_pattern; instantiate_imp = _52_205.instantiate_imp; effects = _52_205.effects; generalize = _52_205.generalize; letrecs = _52_205.letrecs; top_level = _52_205.top_level; check_uvars = _52_205.check_uvars; use_eq = _52_205.use_eq; is_iface = _52_205.is_iface; admit = _52_205.admit; lax = _52_205.lax; type_of = _52_205.type_of; universe_of = _52_205.universe_of; use_bv_sorts = _52_205.use_bv_sorts; qname_and_index = _52_205.qname_and_index}))))))
in (

let pop = (fun env -> (

let _52_209 = (pop_query_indices ())
in (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_214 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_217 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end)))
in (

let mark = (fun env -> (push env))
in (

let commit_mark = (fun env -> (

let _52_222 = (let _144_512 = (pop env)
in (Prims.ignore _144_512))
in env))
in (

let reset_mark = (fun env -> (pop env))
in (

let incr_query_index = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(match ((FStar_All.pipe_right qix (FStar_List.tryFind (fun _52_237 -> (match (_52_237) with
| (m, _52_236) -> begin
(FStar_Ident.lid_equals l m)
end))))) with
| None -> begin
(

let next = (n + 1)
in (

let _52_240 = (add_query_index ((l), (next)))
in (

let _52_242 = env
in {solver = _52_242.solver; range = _52_242.range; curmodule = _52_242.curmodule; gamma = _52_242.gamma; gamma_cache = _52_242.gamma_cache; modules = _52_242.modules; expected_typ = _52_242.expected_typ; sigtab = _52_242.sigtab; is_pattern = _52_242.is_pattern; instantiate_imp = _52_242.instantiate_imp; effects = _52_242.effects; generalize = _52_242.generalize; letrecs = _52_242.letrecs; top_level = _52_242.top_level; check_uvars = _52_242.check_uvars; use_eq = _52_242.use_eq; is_iface = _52_242.is_iface; admit = _52_242.admit; lax = _52_242.lax; type_of = _52_242.type_of; universe_of = _52_242.universe_of; use_bv_sorts = _52_242.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end
| Some (_52_245, m) -> begin
(

let next = (m + 1)
in (

let _52_250 = (add_query_index ((l), (next)))
in (

let _52_252 = env
in {solver = _52_252.solver; range = _52_252.range; curmodule = _52_252.curmodule; gamma = _52_252.gamma; gamma_cache = _52_252.gamma_cache; modules = _52_252.modules; expected_typ = _52_252.expected_typ; sigtab = _52_252.sigtab; is_pattern = _52_252.is_pattern; instantiate_imp = _52_252.instantiate_imp; effects = _52_252.effects; generalize = _52_252.generalize; letrecs = _52_252.letrecs; top_level = _52_252.top_level; check_uvars = _52_252.check_uvars; use_eq = _52_252.use_eq; is_iface = _52_252.is_iface; admit = _52_252.admit; lax = _52_252.lax; type_of = _52_252.type_of; universe_of = _52_252.universe_of; use_bv_sorts = _52_252.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end)
end)))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop; es_incr_query_index = incr_query_index}))))))))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_256 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_259 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_262 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_265 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_269 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let incr_query_index : env  ->  env = (fun env -> (stack_ops.es_incr_query_index env))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_276 = e
in {solver = _52_276.solver; range = r; curmodule = _52_276.curmodule; gamma = _52_276.gamma; gamma_cache = _52_276.gamma_cache; modules = _52_276.modules; expected_typ = _52_276.expected_typ; sigtab = _52_276.sigtab; is_pattern = _52_276.is_pattern; instantiate_imp = _52_276.instantiate_imp; effects = _52_276.effects; generalize = _52_276.generalize; letrecs = _52_276.letrecs; top_level = _52_276.top_level; check_uvars = _52_276.check_uvars; use_eq = _52_276.use_eq; is_iface = _52_276.is_iface; admit = _52_276.admit; lax = _52_276.lax; type_of = _52_276.type_of; universe_of = _52_276.universe_of; use_bv_sorts = _52_276.use_bv_sorts; qname_and_index = _52_276.qname_and_index})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_283 = env
in {solver = _52_283.solver; range = _52_283.range; curmodule = lid; gamma = _52_283.gamma; gamma_cache = _52_283.gamma_cache; modules = _52_283.modules; expected_typ = _52_283.expected_typ; sigtab = _52_283.sigtab; is_pattern = _52_283.is_pattern; instantiate_imp = _52_283.instantiate_imp; effects = _52_283.effects; generalize = _52_283.generalize; letrecs = _52_283.letrecs; top_level = _52_283.top_level; check_uvars = _52_283.check_uvars; use_eq = _52_283.use_eq; is_iface = _52_283.is_iface; admit = _52_283.admit; lax = _52_283.lax; type_of = _52_283.type_of; universe_of = _52_283.universe_of; use_bv_sorts = _52_283.use_bv_sorts; qname_and_index = _52_283.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _144_565 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _144_565)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _52_292 -> (match (()) with
| () -> begin
(let _144_568 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_144_568))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _52_304) -> begin
(

let _52_306 = ()
in (

let n = ((FStar_List.length formals) - 1)
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _144_575 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_144_575))))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_319 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_327 -> (match (_52_327) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_330 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _144_591 = (let _144_590 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _144_589 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _144_588 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _144_587 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _144_590 _144_589 _144_588 _144_587)))))
in (FStar_All.failwith _144_591))
end else begin
()
end
in (let _144_592 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _144_592))))
end
| _52_333 -> begin
(let _144_594 = (let _144_593 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _144_593))
in (FStar_All.failwith _144_594))
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
| ([], _52_344) -> begin
Maybe
end
| (_52_347, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_358 -> begin
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

let _52_364 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _144_614 = (let _144_613 = (inst_tscheme t)
in FStar_Util.Inl (_144_613))
in Some (_144_614))
end else begin
None
end
end
| Binding_sig (_52_373, FStar_Syntax_Syntax.Sig_bundle (ses, _52_376, _52_378, _52_380)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _144_616 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _144_616 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr (((se), (None)))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_393) -> begin
Some (t)
end
| _52_396 -> begin
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
| _52_403 -> begin
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
| Some (_52_413) -> begin
true
end))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_419, _52_421, _52_423) -> begin
(add_sigelts env ses)
end
| _52_427 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let _52_430 = (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_434) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| _52_440 -> begin
()
end)))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_3 -> (match (_52_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_449 -> begin
None
end))))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_4 -> (match (_52_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_456 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_460, (lb)::[]), _52_465, _52_467, _52_469) -> begin
(let _144_650 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_144_650))
end
| FStar_Syntax_Syntax.Sig_let ((_52_473, lbs), _52_477, _52_479, _52_481) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_486) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _144_652 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_144_652))
end else begin
None
end
end)))
end
| _52_491 -> begin
None
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _144_660 = (let _144_659 = (let _144_658 = (variable_not_found bv)
in (let _144_657 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_144_658), (_144_657))))
in FStar_Syntax_Syntax.Error (_144_659))
in (Prims.raise _144_660))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_500) -> begin
(let _144_666 = (let _144_665 = (let _144_664 = (let _144_663 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _144_663))
in ((ne.FStar_Syntax_Syntax.univs), (_144_664)))
in (inst_tscheme _144_665))
in Some (_144_666))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_507, _52_509, _52_511) -> begin
(let _144_670 = (let _144_669 = (let _144_668 = (let _144_667 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _144_667))
in ((us), (_144_668)))
in (inst_tscheme _144_669))
in Some (_144_670))
end
| _52_515 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_525, t) -> begin
Some (t)
end)
end
| _52_530 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (

let mapper = (fun _52_5 -> (match (_52_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_537, uvs, t, _52_541, _52_543, _52_545, _52_547, _52_549), None) -> begin
(let _144_681 = (inst_tscheme ((uvs), (t)))
in Some (_144_681))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_560), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _144_682 = (inst_tscheme ((uvs), (t)))
in Some (_144_682))
end else begin
None
end
end else begin
(let _144_683 = (inst_tscheme ((uvs), (t)))
in Some (_144_683))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_571, _52_573, _52_575, _52_577), None) -> begin
(match (tps) with
| [] -> begin
(let _144_685 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _144_684 -> Some (_144_684)) _144_685))
end
| _52_585 -> begin
(let _144_690 = (let _144_689 = (let _144_688 = (let _144_687 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _144_687))
in ((uvs), (_144_688)))
in (inst_tscheme _144_689))
in (FStar_All.pipe_left (fun _144_686 -> Some (_144_686)) _144_690))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_591, _52_593, _52_595, _52_597), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _144_692 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _144_691 -> Some (_144_691)) _144_692))
end
| _52_606 -> begin
(let _144_697 = (let _144_696 = (let _144_695 = (let _144_694 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _144_694))
in ((uvs), (_144_695)))
in (inst_tscheme_with _144_696 us))
in (FStar_All.pipe_left (fun _144_693 -> Some (_144_693)) _144_697))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_610), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_615 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _144_698 = (lookup_qname env lid)
in (FStar_Util.bind_opt _144_698 mapper))) with
| Some (us, t) -> begin
Some (((us), ((

let _52_621 = t
in {FStar_Syntax_Syntax.n = _52_621.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_621.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_621.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_6 -> (match (_52_6) with
| FStar_Util.Inl (_52_628) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_632) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_636, _52_638, _52_640, qs, _52_643) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_647) -> begin
Some (true)
end
| _52_650 -> begin
Some (false)
end)
end))
in (match ((let _144_705 = (lookup_qname env lid)
in (FStar_Util.bind_opt _144_705 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _144_712 = (let _144_711 = (let _144_710 = (name_not_found l)
in ((_144_710), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_144_711))
in (Prims.raise _144_712))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_663, uvs, t, _52_667, _52_669), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_677 -> begin
(let _144_719 = (let _144_718 = (let _144_717 = (name_not_found lid)
in ((_144_717), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_144_718))
in (Prims.raise _144_719))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_681, uvs, t, _52_685, _52_687, _52_689, _52_691, _52_693), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_701 -> begin
(let _144_726 = (let _144_725 = (let _144_724 = (name_not_found lid)
in ((_144_724), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_144_725))
in (Prims.raise _144_726))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_711, lbs), _52_715, _52_717, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _144_735 = (let _144_734 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in ((lb.FStar_Syntax_Syntax.lbunivs), (_144_734)))
in Some (_144_735))
end else begin
None
end)))
end
| _52_724 -> begin
None
end)
end
| _52_726 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _144_742 = (let _144_741 = (let _144_740 = (name_not_found ftv)
in ((_144_740), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_144_741))
in (Prims.raise _144_742))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_736 -> (match (()) with
| () -> begin
(let _144_753 = (let _144_752 = (FStar_Util.string_of_int i)
in (let _144_751 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _144_752 _144_751)))
in (FStar_All.failwith _144_753))
end))
in (

let _52_740 = (lookup_datacon env lid)
in (match (_52_740) with
| (_52_738, t) -> begin
(match ((let _144_754 = (FStar_Syntax_Subst.compress t)
in _144_754.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_743) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _144_755 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _144_755 Prims.fst)))
end
end
| _52_748 -> begin
(fail ())
end)
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_752, uvs, t, q, _52_757), None)) -> begin
Some (((((uvs), (t))), (q)))
end
| _52_765 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_775), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_785 -> begin
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
| ([], _52_789) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_792, (_52_799)::(_52_796)::_52_794) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _144_769 = (let _144_768 = (FStar_Syntax_Print.lid_to_string lid)
in (let _144_767 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _144_768 _144_767)))
in (FStar_All.failwith _144_769))
end
| _52_803 -> begin
(

let _52_807 = (let _144_771 = (let _144_770 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_144_770)))
in (inst_tscheme_with _144_771 insts))
in (match (_52_807) with
| (_52_805, t) -> begin
(match ((let _144_772 = (FStar_Syntax_Subst.compress t)
in _144_772.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| _52_813 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_815 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create 20)
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_823, c) -> begin
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

let _52_837 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_843, _52_845, _52_847, _52_849, _52_851, dcs, _52_854, _52_856), _52_860)) -> begin
dcs
end
| _52_865 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_869, _52_871, _52_873, l, _52_876, _52_878, _52_880, _52_882), _52_886)) -> begin
l
end
| _52_891 -> begin
(let _144_788 = (let _144_787 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _144_787))
in (FStar_All.failwith _144_788))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_895, _52_897, _52_899, _52_901, _52_903, _52_905, _52_907, _52_909), _52_913)) -> begin
true
end
| _52_918 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_922, _52_924, _52_926, _52_928, _52_930, _52_932, tags, _52_935), _52_939)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_951 -> begin
false
end)) tags)
end
| _52_953 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_957, _52_959, _52_961, quals, _52_964), _52_968)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_974) -> begin
true
end
| _52_977 -> begin
false
end)) quals)
end
| _52_979 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _144_807 = (FStar_Syntax_Util.un_uinst head)
in _144_807.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_985 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _144_819 = (let _144_818 = (let _144_817 = (name_not_found l)
in ((_144_817), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_144_818))
in (Prims.raise _144_819))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_1013 -> (match (_52_1013) with
| (m1, m2, _52_1008, _52_1010, _52_1012) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _144_895 = (let _144_894 = (let _144_893 = (let _144_892 = (FStar_Syntax_Print.lid_to_string l1)
in (let _144_891 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _144_892 _144_891)))
in ((_144_893), (env.range)))
in FStar_Syntax_Syntax.Error (_144_894))
in (Prims.raise _144_895))
end
| Some (_52_1016, _52_1018, m3, j1, j2) -> begin
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
(let _144_910 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _144_910))
end
| Some (md) -> begin
(

let _52_1039 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_52_1039) with
| (_52_1037, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_1048))::((wp, _52_1044))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _52_1056 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_1063) -> begin
(

let effects = (

let _52_1066 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1066.order; joins = _52_1066.joins})
in (

let _52_1069 = env
in {solver = _52_1069.solver; range = _52_1069.range; curmodule = _52_1069.curmodule; gamma = _52_1069.gamma; gamma_cache = _52_1069.gamma_cache; modules = _52_1069.modules; expected_typ = _52_1069.expected_typ; sigtab = _52_1069.sigtab; is_pattern = _52_1069.is_pattern; instantiate_imp = _52_1069.instantiate_imp; effects = effects; generalize = _52_1069.generalize; letrecs = _52_1069.letrecs; top_level = _52_1069.top_level; check_uvars = _52_1069.check_uvars; use_eq = _52_1069.use_eq; is_iface = _52_1069.is_iface; admit = _52_1069.admit; lax = _52_1069.lax; type_of = _52_1069.type_of; universe_of = _52_1069.universe_of; use_bv_sorts = _52_1069.use_bv_sorts; qname_and_index = _52_1069.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1073) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _144_925 = (e1.mlift r wp1)
in (e2.mlift r _144_925)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1088 = (inst_tscheme lift_t)
in (match (_52_1088) with
| (_52_1086, lift_t) -> begin
(let _144_937 = (let _144_936 = (let _144_935 = (let _144_934 = (FStar_Syntax_Syntax.as_arg r)
in (let _144_933 = (let _144_932 = (FStar_Syntax_Syntax.as_arg wp1)
in (_144_932)::[])
in (_144_934)::_144_933))
in ((lift_t), (_144_935)))
in FStar_Syntax_Syntax.Tm_app (_144_936))
in (FStar_Syntax_Syntax.mk _144_937 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift_wp)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _144_954 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _144_954 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _144_955 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _144_955 FStar_Syntax_Syntax.Delta_constant None))
in (let _144_956 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _144_956)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1105 -> (match (_52_1105) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _144_962 -> Some (_144_962)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _144_970 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _144_969 = (find_edge order ((i), (k)))
in (let _144_968 = (find_edge order ((k), (j)))
in ((_144_969), (_144_968))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1117 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _144_970))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _144_1062 = (find_edge order ((i), (k)))
in (let _144_1061 = (find_edge order ((j), (k)))
in ((_144_1062), (_144_1061))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _52_1134, _52_1136) -> begin
if ((let _144_1063 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _144_1063)) && (not ((let _144_1064 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _144_1064))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _52_1140 -> begin
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

let _52_1149 = env.effects
in {decls = _52_1149.decls; order = order; joins = joins})
in (

let _52_1152 = env
in {solver = _52_1152.solver; range = _52_1152.range; curmodule = _52_1152.curmodule; gamma = _52_1152.gamma; gamma_cache = _52_1152.gamma_cache; modules = _52_1152.modules; expected_typ = _52_1152.expected_typ; sigtab = _52_1152.sigtab; is_pattern = _52_1152.is_pattern; instantiate_imp = _52_1152.instantiate_imp; effects = effects; generalize = _52_1152.generalize; letrecs = _52_1152.letrecs; top_level = _52_1152.top_level; check_uvars = _52_1152.check_uvars; use_eq = _52_1152.use_eq; is_iface = _52_1152.is_iface; admit = _52_1152.admit; lax = _52_1152.lax; type_of = _52_1152.type_of; universe_of = _52_1152.universe_of; use_bv_sorts = _52_1152.use_bv_sorts; qname_and_index = _52_1152.qname_and_index})))))))))))))
end
| _52_1155 -> begin
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
(let _144_1113 = (push x rest)
in (local)::_144_1113)
end))
in (

let _52_1177 = env
in (let _144_1114 = (push s env.gamma)
in {solver = _52_1177.solver; range = _52_1177.range; curmodule = _52_1177.curmodule; gamma = _144_1114; gamma_cache = _52_1177.gamma_cache; modules = _52_1177.modules; expected_typ = _52_1177.expected_typ; sigtab = _52_1177.sigtab; is_pattern = _52_1177.is_pattern; instantiate_imp = _52_1177.instantiate_imp; effects = _52_1177.effects; generalize = _52_1177.generalize; letrecs = _52_1177.letrecs; top_level = _52_1177.top_level; check_uvars = _52_1177.check_uvars; use_eq = _52_1177.use_eq; is_iface = _52_1177.is_iface; admit = _52_1177.admit; lax = _52_1177.lax; type_of = _52_1177.type_of; universe_of = _52_1177.universe_of; use_bv_sorts = _52_1177.use_bv_sorts; qname_and_index = _52_1177.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (let _144_1121 = (let _144_1120 = (let _144_1119 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_144_1119), (s)))
in Binding_sig (_144_1120))
in (push_in_gamma env _144_1121))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (let _144_1130 = (let _144_1129 = (let _144_1128 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_144_1128), (s), (us)))
in Binding_sig_inst (_144_1129))
in (push_in_gamma env _144_1130))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1188 = env
in {solver = _52_1188.solver; range = _52_1188.range; curmodule = _52_1188.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1188.gamma_cache; modules = _52_1188.modules; expected_typ = _52_1188.expected_typ; sigtab = _52_1188.sigtab; is_pattern = _52_1188.is_pattern; instantiate_imp = _52_1188.instantiate_imp; effects = _52_1188.effects; generalize = _52_1188.generalize; letrecs = _52_1188.letrecs; top_level = _52_1188.top_level; check_uvars = _52_1188.check_uvars; use_eq = _52_1188.use_eq; is_iface = _52_1188.is_iface; admit = _52_1188.admit; lax = _52_1188.lax; type_of = _52_1188.type_of; universe_of = _52_1188.universe_of; use_bv_sorts = _52_1188.use_bv_sorts; qname_and_index = _52_1188.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1198 -> (match (_52_1198) with
| (x, _52_1197) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1203 = ()
in (

let x = (

let _52_1205 = x
in {FStar_Syntax_Syntax.ppname = _52_1205.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1205.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1215 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1217 = env
in {solver = _52_1217.solver; range = _52_1217.range; curmodule = _52_1217.curmodule; gamma = []; gamma_cache = _52_1217.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1217.sigtab; is_pattern = _52_1217.is_pattern; instantiate_imp = _52_1217.instantiate_imp; effects = _52_1217.effects; generalize = _52_1217.generalize; letrecs = _52_1217.letrecs; top_level = _52_1217.top_level; check_uvars = _52_1217.check_uvars; use_eq = _52_1217.use_eq; is_iface = _52_1217.is_iface; admit = _52_1217.admit; lax = _52_1217.lax; type_of = _52_1217.type_of; universe_of = _52_1217.universe_of; use_bv_sorts = _52_1217.use_bv_sorts; qname_and_index = _52_1217.qname_and_index})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1225 = env
in {solver = _52_1225.solver; range = _52_1225.range; curmodule = _52_1225.curmodule; gamma = _52_1225.gamma; gamma_cache = _52_1225.gamma_cache; modules = _52_1225.modules; expected_typ = Some (t); sigtab = _52_1225.sigtab; is_pattern = _52_1225.is_pattern; instantiate_imp = _52_1225.instantiate_imp; effects = _52_1225.effects; generalize = _52_1225.generalize; letrecs = _52_1225.letrecs; top_level = _52_1225.top_level; check_uvars = _52_1225.check_uvars; use_eq = false; is_iface = _52_1225.is_iface; admit = _52_1225.admit; lax = _52_1225.lax; type_of = _52_1225.type_of; universe_of = _52_1225.universe_of; use_bv_sorts = _52_1225.use_bv_sorts; qname_and_index = _52_1225.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _144_1173 = (expected_typ env)
in (((

let _52_1232 = env
in {solver = _52_1232.solver; range = _52_1232.range; curmodule = _52_1232.curmodule; gamma = _52_1232.gamma; gamma_cache = _52_1232.gamma_cache; modules = _52_1232.modules; expected_typ = None; sigtab = _52_1232.sigtab; is_pattern = _52_1232.is_pattern; instantiate_imp = _52_1232.instantiate_imp; effects = _52_1232.effects; generalize = _52_1232.generalize; letrecs = _52_1232.letrecs; top_level = _52_1232.top_level; check_uvars = _52_1232.check_uvars; use_eq = false; is_iface = _52_1232.is_iface; admit = _52_1232.admit; lax = _52_1232.lax; type_of = _52_1232.type_of; universe_of = _52_1232.universe_of; use_bv_sorts = _52_1232.use_bv_sorts; qname_and_index = _52_1232.qname_and_index})), (_144_1173))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _144_1179 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1239, se) -> begin
(se)::[]
end
| _52_1244 -> begin
[]
end))))
in (FStar_All.pipe_right _144_1179 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1246 = (add_sigelts env sigs)
in (

let _52_1248 = env
in {solver = _52_1248.solver; range = _52_1248.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1248.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1248.expected_typ; sigtab = _52_1248.sigtab; is_pattern = _52_1248.is_pattern; instantiate_imp = _52_1248.instantiate_imp; effects = _52_1248.effects; generalize = _52_1248.generalize; letrecs = _52_1248.letrecs; top_level = _52_1248.top_level; check_uvars = _52_1248.check_uvars; use_eq = _52_1248.use_eq; is_iface = _52_1248.is_iface; admit = _52_1248.admit; lax = _52_1248.lax; type_of = _52_1248.type_of; universe_of = _52_1248.universe_of; use_bv_sorts = _52_1248.use_bv_sorts; qname_and_index = _52_1248.qname_and_index})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1261))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _144_1191 = (let _144_1190 = (FStar_Syntax_Free.uvars t)
in (ext out _144_1190))
in (aux _144_1191 tl))
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
(let _144_1203 = (let _144_1202 = (FStar_Syntax_Free.univs t)
in (ext out _144_1202))
in (aux _144_1203 tl))
end
| (Binding_sig (_52_1331))::_52_1329 -> begin
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


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _144_1210 = (let _144_1209 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _144_1209 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _144_1210 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1363) -> begin
(FStar_List.append lids keys)
end
| _52_1367 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1369 v keys -> (let _144_1233 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _144_1233 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1373 -> ()); push = (fun _52_1375 -> ()); pop = (fun _52_1377 -> ()); mark = (fun _52_1379 -> ()); reset_mark = (fun _52_1381 -> ()); commit_mark = (fun _52_1383 -> ()); encode_modul = (fun _52_1385 _52_1387 -> ()); encode_sig = (fun _52_1389 _52_1391 -> ()); solve = (fun _52_1393 _52_1395 _52_1397 -> ()); is_trivial = (fun _52_1399 _52_1401 -> false); finish = (fun _52_1403 -> ()); refresh = (fun _52_1404 -> ())}




