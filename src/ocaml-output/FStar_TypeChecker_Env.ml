
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
in (let _146_395 = (aux l1 l2)
in Unfold (_146_395)))
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun _52_159 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _52_160 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _146_427 = (new_gamma_cache ())
in (let _146_426 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _146_427; modules = []; expected_typ = None; sigtab = _146_426; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


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
(let _146_492 = (let _146_491 = (let _146_489 = (FStar_ST.read query_indices)
in (FStar_List.hd _146_489))
in (let _146_490 = (FStar_ST.read query_indices)
in (_146_491)::_146_490))
in (FStar_ST.op_Colon_Equals query_indices _146_492))
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
(let _146_499 = (FStar_ST.read query_indices)
in (FStar_List.hd _146_499))
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

let _52_210 = (let _146_505 = (let _146_504 = (FStar_ST.read stack)
in (env)::_146_504)
in (FStar_ST.op_Colon_Equals stack _146_505))
in (

let _52_212 = env
in (let _146_507 = (FStar_Util.smap_copy (gamma_cache env))
in (let _146_506 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_212.solver; range = _52_212.range; curmodule = _52_212.curmodule; gamma = _52_212.gamma; gamma_cache = _146_507; modules = _52_212.modules; expected_typ = _52_212.expected_typ; sigtab = _146_506; is_pattern = _52_212.is_pattern; instantiate_imp = _52_212.instantiate_imp; effects = _52_212.effects; generalize = _52_212.generalize; letrecs = _52_212.letrecs; top_level = _52_212.top_level; check_uvars = _52_212.check_uvars; use_eq = _52_212.use_eq; is_iface = _52_212.is_iface; admit = _52_212.admit; lax = _52_212.lax; type_of = _52_212.type_of; universe_of = _52_212.universe_of; use_bv_sorts = _52_212.use_bv_sorts; qname_and_index = _52_212.qname_and_index})))))
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

let _52_239 = (let _146_518 = (pop_stack env)
in (Prims.ignore _146_518))
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

let next = (n + (Prims.parse_int "1"))
in (

let _52_259 = (add_query_index ((l), (next)))
in (

let _52_261 = env
in {solver = _52_261.solver; range = _52_261.range; curmodule = _52_261.curmodule; gamma = _52_261.gamma; gamma_cache = _52_261.gamma_cache; modules = _52_261.modules; expected_typ = _52_261.expected_typ; sigtab = _52_261.sigtab; is_pattern = _52_261.is_pattern; instantiate_imp = _52_261.instantiate_imp; effects = _52_261.effects; generalize = _52_261.generalize; letrecs = _52_261.letrecs; top_level = _52_261.top_level; check_uvars = _52_261.check_uvars; use_eq = _52_261.use_eq; is_iface = _52_261.is_iface; admit = _52_261.admit; lax = _52_261.lax; type_of = _52_261.type_of; universe_of = _52_261.universe_of; use_bv_sorts = _52_261.use_bv_sorts; qname_and_index = Some (((l), (next)))})))
end
| Some (_52_264, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
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


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _146_571 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _146_571)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _52_311 -> (match (()) with
| () -> begin
(let _146_574 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_146_574))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _52_323) -> begin
(

let _52_325 = ()
in (

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _146_581 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_146_581))))))
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
(let _146_597 = (let _146_596 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _146_595 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _146_594 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_593 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _146_596 _146_595 _146_594 _146_593)))))
in (FStar_All.failwith _146_597))
end else begin
()
end
in (let _146_598 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _146_598))))
end
| _52_352 -> begin
(let _146_600 = (let _146_599 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _146_599))
in (FStar_All.failwith _146_600))
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
(let _146_620 = (let _146_619 = (inst_tscheme t)
in FStar_Util.Inl (_146_619))
in Some (_146_620))
end else begin
None
end
end
| Binding_sig (_52_392, FStar_Syntax_Syntax.Sig_bundle (ses, _52_395, _52_397, _52_399)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _146_622 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _146_622 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
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
(let _146_656 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_146_656))
end
| FStar_Syntax_Syntax.Sig_let ((_52_492, lbs), _52_496, _52_498, _52_500) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_505) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _146_658 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_146_658))
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
(let _146_666 = (let _146_665 = (let _146_664 = (variable_not_found bv)
in (let _146_663 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_146_664), (_146_663))))
in FStar_Syntax_Syntax.Error (_146_665))
in (Prims.raise _146_666))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_519) -> begin
(let _146_672 = (let _146_671 = (let _146_670 = (let _146_669 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _146_669))
in ((ne.FStar_Syntax_Syntax.univs), (_146_670)))
in (inst_tscheme _146_671))
in Some (_146_672))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_526, _52_528, _52_530) -> begin
(let _146_676 = (let _146_675 = (let _146_674 = (let _146_673 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _146_673))
in ((us), (_146_674)))
in (inst_tscheme _146_675))
in Some (_146_676))
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
(let _146_687 = (inst_tscheme ((uvs), (t)))
in Some (_146_687))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_579), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _146_688 = (inst_tscheme ((uvs), (t)))
in Some (_146_688))
end else begin
None
end
end else begin
(let _146_689 = (inst_tscheme ((uvs), (t)))
in Some (_146_689))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_590, _52_592, _52_594, _52_596), None) -> begin
(match (tps) with
| [] -> begin
(let _146_691 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _146_690 -> Some (_146_690)) _146_691))
end
| _52_604 -> begin
(let _146_696 = (let _146_695 = (let _146_694 = (let _146_693 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _146_693))
in ((uvs), (_146_694)))
in (inst_tscheme _146_695))
in (FStar_All.pipe_left (fun _146_692 -> Some (_146_692)) _146_696))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_610, _52_612, _52_614, _52_616), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _146_698 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _146_697 -> Some (_146_697)) _146_698))
end
| _52_625 -> begin
(let _146_703 = (let _146_702 = (let _146_701 = (let _146_700 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _146_700))
in ((uvs), (_146_701)))
in (inst_tscheme_with _146_702 us))
in (FStar_All.pipe_left (fun _146_699 -> Some (_146_699)) _146_703))
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
in (match ((let _146_704 = (lookup_qname env lid)
in (FStar_Util.bind_opt _146_704 mapper))) with
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
in (match ((let _146_711 = (lookup_qname env lid)
in (FStar_Util.bind_opt _146_711 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _146_718 = (let _146_717 = (let _146_716 = (name_not_found l)
in ((_146_716), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_146_717))
in (Prims.raise _146_718))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_682, uvs, t, _52_686, _52_688), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_696 -> begin
(let _146_725 = (let _146_724 = (let _146_723 = (name_not_found lid)
in ((_146_723), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_146_724))
in (Prims.raise _146_725))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_700, uvs, t, _52_704, _52_706, _52_708, _52_710, _52_712), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_720 -> begin
(let _146_732 = (let _146_731 = (let _146_730 = (name_not_found lid)
in ((_146_730), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_146_731))
in (Prims.raise _146_732))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_730, lbs), _52_734, _52_736, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _146_741 = (let _146_740 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in ((lb.FStar_Syntax_Syntax.lbunivs), (_146_740)))
in Some (_146_741))
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
(let _146_748 = (let _146_747 = (let _146_746 = (name_not_found ftv)
in ((_146_746), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_146_747))
in (Prims.raise _146_748))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_755 -> (match (()) with
| () -> begin
(let _146_759 = (let _146_758 = (FStar_Util.string_of_int i)
in (let _146_757 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _146_758 _146_757)))
in (FStar_All.failwith _146_759))
end))
in (

let _52_759 = (lookup_datacon env lid)
in (match (_52_759) with
| (_52_757, t) -> begin
(match ((let _146_760 = (FStar_Syntax_Subst.compress t)
in _146_760.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_762) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _146_761 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _146_761 Prims.fst)))
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
(let _146_775 = (let _146_774 = (FStar_Syntax_Print.lid_to_string lid)
in (let _146_773 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _146_774 _146_773)))
in (FStar_All.failwith _146_775))
end
| _52_822 -> begin
(

let _52_826 = (let _146_777 = (let _146_776 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_146_776)))
in (inst_tscheme_with _146_777 insts))
in (match (_52_826) with
| (_52_824, t) -> begin
(match ((let _146_778 = (FStar_Syntax_Subst.compress t)
in _146_778.FStar_Syntax_Syntax.n)) with
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

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_842, c) -> begin
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

let _52_856 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l = (norm_eff_name env l)
in (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, _52_864), _52_868)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| _52_873 -> begin
[]
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_877, _52_879, _52_881, _52_883, _52_885, dcs, _52_888, _52_890), _52_894)) -> begin
dcs
end
| _52_899 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_903, _52_905, _52_907, l, _52_910, _52_912, _52_914, _52_916), _52_920)) -> begin
l
end
| _52_925 -> begin
(let _146_798 = (let _146_797 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _146_797))
in (FStar_All.failwith _146_798))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_929, _52_931, _52_933, _52_935, _52_937, _52_939, _52_941, _52_943), _52_947)) -> begin
true
end
| _52_952 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_956, _52_958, _52_960, _52_962, _52_964, _52_966, tags, _52_969), _52_973)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_985 -> begin
false
end)) tags)
end
| _52_987 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_991, _52_993, _52_995, quals, _52_998), _52_1002)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_1008) -> begin
true
end
| _52_1011 -> begin
false
end)) quals)
end
| _52_1013 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _146_817 = (FStar_Syntax_Util.un_uinst head)
in _146_817.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_1019 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _146_829 = (let _146_828 = (let _146_827 = (name_not_found l)
in ((_146_827), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_146_828))
in (Prims.raise _146_829))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_1047 -> (match (_52_1047) with
| (m1, m2, _52_1042, _52_1044, _52_1046) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _146_905 = (let _146_904 = (let _146_903 = (let _146_902 = (FStar_Syntax_Print.lid_to_string l1)
in (let _146_901 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _146_902 _146_901)))
in ((_146_903), (env.range)))
in FStar_Syntax_Syntax.Error (_146_904))
in (Prims.raise _146_905))
end
| Some (_52_1050, _52_1052, m3, j1, j2) -> begin
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
(let _146_920 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _146_920))
end
| Some (md) -> begin
(

let _52_1073 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_52_1073) with
| (_52_1071, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_1082))::((wp, _52_1078))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _52_1090 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_1097) -> begin
(

let effects = (

let _52_1100 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1100.order; joins = _52_1100.joins})
in (

let _52_1103 = env
in {solver = _52_1103.solver; range = _52_1103.range; curmodule = _52_1103.curmodule; gamma = _52_1103.gamma; gamma_cache = _52_1103.gamma_cache; modules = _52_1103.modules; expected_typ = _52_1103.expected_typ; sigtab = _52_1103.sigtab; is_pattern = _52_1103.is_pattern; instantiate_imp = _52_1103.instantiate_imp; effects = effects; generalize = _52_1103.generalize; letrecs = _52_1103.letrecs; top_level = _52_1103.top_level; check_uvars = _52_1103.check_uvars; use_eq = _52_1103.use_eq; is_iface = _52_1103.is_iface; admit = _52_1103.admit; lax = _52_1103.lax; type_of = _52_1103.type_of; universe_of = _52_1103.universe_of; use_bv_sorts = _52_1103.use_bv_sorts; qname_and_index = _52_1103.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1107) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _146_935 = (e1.mlift r wp1)
in (e2.mlift r _146_935)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1122 = (inst_tscheme lift_t)
in (match (_52_1122) with
| (_52_1120, lift_t) -> begin
(let _146_947 = (let _146_946 = (let _146_945 = (let _146_944 = (FStar_Syntax_Syntax.as_arg r)
in (let _146_943 = (let _146_942 = (FStar_Syntax_Syntax.as_arg wp1)
in (_146_942)::[])
in (_146_944)::_146_943))
in ((lift_t), (_146_945)))
in FStar_Syntax_Syntax.Tm_app (_146_946))
in (FStar_Syntax_Syntax.mk _146_947 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift_wp)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _146_964 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _146_964 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _146_965 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _146_965 FStar_Syntax_Syntax.Delta_constant None))
in (let _146_966 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _146_966)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1139 -> (match (_52_1139) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _146_972 -> Some (_146_972)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _146_980 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _146_979 = (find_edge order ((i), (k)))
in (let _146_978 = (find_edge order ((k), (j)))
in ((_146_979), (_146_978))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1151 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _146_980))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let _52_1157 = (FStar_All.pipe_right order (FStar_List.iter (fun edge -> if ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (let _146_984 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right _146_984 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))) then begin
(let _146_988 = (let _146_987 = (let _146_986 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (let _146_985 = (get_range env)
in ((_146_986), (_146_985))))
in FStar_Syntax_Syntax.Error (_146_987))
in (Prims.raise _146_988))
end else begin
()
end)))
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _146_1078 = (find_edge order ((i), (k)))
in (let _146_1077 = (find_edge order ((j), (k)))
in ((_146_1078), (_146_1077))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _52_1171, _52_1173) -> begin
if ((let _146_1079 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _146_1079)) && (not ((let _146_1080 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _146_1080))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _52_1177 -> begin
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

let _52_1186 = env.effects
in {decls = _52_1186.decls; order = order; joins = joins})
in (

let _52_1189 = env
in {solver = _52_1189.solver; range = _52_1189.range; curmodule = _52_1189.curmodule; gamma = _52_1189.gamma; gamma_cache = _52_1189.gamma_cache; modules = _52_1189.modules; expected_typ = _52_1189.expected_typ; sigtab = _52_1189.sigtab; is_pattern = _52_1189.is_pattern; instantiate_imp = _52_1189.instantiate_imp; effects = effects; generalize = _52_1189.generalize; letrecs = _52_1189.letrecs; top_level = _52_1189.top_level; check_uvars = _52_1189.check_uvars; use_eq = _52_1189.use_eq; is_iface = _52_1189.is_iface; admit = _52_1189.admit; lax = _52_1189.lax; type_of = _52_1189.type_of; universe_of = _52_1189.universe_of; use_bv_sorts = _52_1189.use_bv_sorts; qname_and_index = _52_1189.qname_and_index}))))))))))))))
end
| _52_1192 -> begin
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
(let _146_1129 = (push x rest)
in (local)::_146_1129)
end))
in (

let _52_1214 = env
in (let _146_1130 = (push s env.gamma)
in {solver = _52_1214.solver; range = _52_1214.range; curmodule = _52_1214.curmodule; gamma = _146_1130; gamma_cache = _52_1214.gamma_cache; modules = _52_1214.modules; expected_typ = _52_1214.expected_typ; sigtab = _52_1214.sigtab; is_pattern = _52_1214.is_pattern; instantiate_imp = _52_1214.instantiate_imp; effects = _52_1214.effects; generalize = _52_1214.generalize; letrecs = _52_1214.letrecs; top_level = _52_1214.top_level; check_uvars = _52_1214.check_uvars; use_eq = _52_1214.use_eq; is_iface = _52_1214.is_iface; admit = _52_1214.admit; lax = _52_1214.lax; type_of = _52_1214.type_of; universe_of = _52_1214.universe_of; use_bv_sorts = _52_1214.use_bv_sorts; qname_and_index = _52_1214.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (let _146_1137 = (let _146_1136 = (let _146_1135 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_146_1135), (s)))
in Binding_sig (_146_1136))
in (push_in_gamma env _146_1137))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (let _146_1146 = (let _146_1145 = (let _146_1144 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_146_1144), (s), (us)))
in Binding_sig_inst (_146_1145))
in (push_in_gamma env _146_1146))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1225 = env
in {solver = _52_1225.solver; range = _52_1225.range; curmodule = _52_1225.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1225.gamma_cache; modules = _52_1225.modules; expected_typ = _52_1225.expected_typ; sigtab = _52_1225.sigtab; is_pattern = _52_1225.is_pattern; instantiate_imp = _52_1225.instantiate_imp; effects = _52_1225.effects; generalize = _52_1225.generalize; letrecs = _52_1225.letrecs; top_level = _52_1225.top_level; check_uvars = _52_1225.check_uvars; use_eq = _52_1225.use_eq; is_iface = _52_1225.is_iface; admit = _52_1225.admit; lax = _52_1225.lax; type_of = _52_1225.type_of; universe_of = _52_1225.universe_of; use_bv_sorts = _52_1225.use_bv_sorts; qname_and_index = _52_1225.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1235 -> (match (_52_1235) with
| (x, _52_1234) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1240 = ()
in (

let x = (

let _52_1242 = x
in {FStar_Syntax_Syntax.ppname = _52_1242.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1242.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1252 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1254 = env
in {solver = _52_1254.solver; range = _52_1254.range; curmodule = _52_1254.curmodule; gamma = []; gamma_cache = _52_1254.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1254.sigtab; is_pattern = _52_1254.is_pattern; instantiate_imp = _52_1254.instantiate_imp; effects = _52_1254.effects; generalize = _52_1254.generalize; letrecs = _52_1254.letrecs; top_level = _52_1254.top_level; check_uvars = _52_1254.check_uvars; use_eq = _52_1254.use_eq; is_iface = _52_1254.is_iface; admit = _52_1254.admit; lax = _52_1254.lax; type_of = _52_1254.type_of; universe_of = _52_1254.universe_of; use_bv_sorts = _52_1254.use_bv_sorts; qname_and_index = _52_1254.qname_and_index})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1262 = env
in {solver = _52_1262.solver; range = _52_1262.range; curmodule = _52_1262.curmodule; gamma = _52_1262.gamma; gamma_cache = _52_1262.gamma_cache; modules = _52_1262.modules; expected_typ = Some (t); sigtab = _52_1262.sigtab; is_pattern = _52_1262.is_pattern; instantiate_imp = _52_1262.instantiate_imp; effects = _52_1262.effects; generalize = _52_1262.generalize; letrecs = _52_1262.letrecs; top_level = _52_1262.top_level; check_uvars = _52_1262.check_uvars; use_eq = false; is_iface = _52_1262.is_iface; admit = _52_1262.admit; lax = _52_1262.lax; type_of = _52_1262.type_of; universe_of = _52_1262.universe_of; use_bv_sorts = _52_1262.use_bv_sorts; qname_and_index = _52_1262.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _146_1189 = (expected_typ env)
in (((

let _52_1269 = env
in {solver = _52_1269.solver; range = _52_1269.range; curmodule = _52_1269.curmodule; gamma = _52_1269.gamma; gamma_cache = _52_1269.gamma_cache; modules = _52_1269.modules; expected_typ = None; sigtab = _52_1269.sigtab; is_pattern = _52_1269.is_pattern; instantiate_imp = _52_1269.instantiate_imp; effects = _52_1269.effects; generalize = _52_1269.generalize; letrecs = _52_1269.letrecs; top_level = _52_1269.top_level; check_uvars = _52_1269.check_uvars; use_eq = false; is_iface = _52_1269.is_iface; admit = _52_1269.admit; lax = _52_1269.lax; type_of = _52_1269.type_of; universe_of = _52_1269.universe_of; use_bv_sorts = _52_1269.use_bv_sorts; qname_and_index = _52_1269.qname_and_index})), (_146_1189))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _146_1195 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1276, se) -> begin
(se)::[]
end
| _52_1281 -> begin
[]
end))))
in (FStar_All.pipe_right _146_1195 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1283 = (add_sigelts env sigs)
in (

let _52_1285 = env
in {solver = _52_1285.solver; range = _52_1285.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1285.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1285.expected_typ; sigtab = _52_1285.sigtab; is_pattern = _52_1285.is_pattern; instantiate_imp = _52_1285.instantiate_imp; effects = _52_1285.effects; generalize = _52_1285.generalize; letrecs = _52_1285.letrecs; top_level = _52_1285.top_level; check_uvars = _52_1285.check_uvars; use_eq = _52_1285.use_eq; is_iface = _52_1285.is_iface; admit = _52_1285.admit; lax = _52_1285.lax; type_of = _52_1285.type_of; universe_of = _52_1285.universe_of; use_bv_sorts = _52_1285.use_bv_sorts; qname_and_index = _52_1285.qname_and_index})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1298))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _146_1207 = (let _146_1206 = (FStar_Syntax_Free.uvars t)
in (ext out _146_1206))
in (aux _146_1207 tl))
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
(let _146_1219 = (let _146_1218 = (FStar_Syntax_Free.univs t)
in (ext out _146_1218))
in (aux _146_1219 tl))
end
| (Binding_sig (_52_1368))::_52_1366 -> begin
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


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _146_1226 = (let _146_1225 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _146_1225 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _146_1226 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1400) -> begin
(FStar_List.append lids keys)
end
| _52_1404 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1406 v keys -> (let _146_1249 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _146_1249 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1410 -> ()); push = (fun _52_1412 -> ()); pop = (fun _52_1414 -> ()); mark = (fun _52_1416 -> ()); reset_mark = (fun _52_1418 -> ()); commit_mark = (fun _52_1420 -> ()); encode_modul = (fun _52_1422 _52_1424 -> ()); encode_sig = (fun _52_1426 _52_1428 -> ()); solve = (fun _52_1430 _52_1432 _52_1434 -> ()); is_trivial = (fun _52_1436 _52_1438 -> false); finish = (fun _52_1440 -> ()); refresh = (fun _52_1441 -> ())}




