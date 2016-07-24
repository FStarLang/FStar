
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool} 
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


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _52_102 -> begin
false
end))


let glb_delta : delta_level  ->  delta_level  ->  delta_level = (fun d1 d2 -> (match ((d1, d2)) with
| ((NoDelta, _)) | ((_, NoDelta)) -> begin
NoDelta
end
| ((OnlyInline, _)) | ((_, OnlyInline)) -> begin
OnlyInline
end
| (Unfold (l1), Unfold (l2)) -> begin
(

let rec aux = (fun l1 l2 -> (match ((l1, l2)) with
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
| (FStar_Syntax_Syntax.Delta_abstract (l1), _52_151) -> begin
(aux l1 l2)
end
| (_52_154, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _143_392 = (aux l1 l2)
in Unfold (_143_392)))
end))


let default_table_size : Prims.int = 200


let new_sigtab = (fun _52_158 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _52_159 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _143_414 = (new_gamma_cache ())
in (let _143_413 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _143_414; modules = []; expected_typ = None; sigtab = _143_413; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _52_176 = (let _143_468 = (let _143_467 = (FStar_ST.read stack)
in (env)::_143_467)
in (FStar_ST.op_Colon_Equals stack _143_468))
in (

let _52_178 = env
in (let _143_470 = (FStar_Util.smap_copy (gamma_cache env))
in (let _143_469 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_178.solver; range = _52_178.range; curmodule = _52_178.curmodule; gamma = _52_178.gamma; gamma_cache = _143_470; modules = _52_178.modules; expected_typ = _52_178.expected_typ; sigtab = _143_469; is_pattern = _52_178.is_pattern; instantiate_imp = _52_178.instantiate_imp; effects = _52_178.effects; generalize = _52_178.generalize; letrecs = _52_178.letrecs; top_level = _52_178.top_level; check_uvars = _52_178.check_uvars; use_eq = _52_178.use_eq; is_iface = _52_178.is_iface; admit = _52_178.admit; lax = _52_178.lax; type_of = _52_178.type_of; universe_of = _52_178.universe_of; use_bv_sorts = _52_178.use_bv_sorts})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_185 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_188 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let mark = (fun env -> (push env))
in (

let commit_mark = (fun env -> (

let _52_193 = (let _143_477 = (pop env)
in (Prims.ignore _143_477))
in env))
in (

let reset_mark = (fun env -> (pop env))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop}))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_199 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_202 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_205 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_208 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_212 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_218 = e
in {solver = _52_218.solver; range = r; curmodule = _52_218.curmodule; gamma = _52_218.gamma; gamma_cache = _52_218.gamma_cache; modules = _52_218.modules; expected_typ = _52_218.expected_typ; sigtab = _52_218.sigtab; is_pattern = _52_218.is_pattern; instantiate_imp = _52_218.instantiate_imp; effects = _52_218.effects; generalize = _52_218.generalize; letrecs = _52_218.letrecs; top_level = _52_218.top_level; check_uvars = _52_218.check_uvars; use_eq = _52_218.use_eq; is_iface = _52_218.is_iface; admit = _52_218.admit; lax = _52_218.lax; type_of = _52_218.type_of; universe_of = _52_218.universe_of; use_bv_sorts = _52_218.use_bv_sorts})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_225 = env
in {solver = _52_225.solver; range = _52_225.range; curmodule = lid; gamma = _52_225.gamma; gamma_cache = _52_225.gamma_cache; modules = _52_225.modules; expected_typ = _52_225.expected_typ; sigtab = _52_225.sigtab; is_pattern = _52_225.is_pattern; instantiate_imp = _52_225.instantiate_imp; effects = _52_225.effects; generalize = _52_225.generalize; letrecs = _52_225.letrecs; top_level = _52_225.top_level; check_uvars = _52_225.check_uvars; use_eq = _52_225.use_eq; is_iface = _52_225.is_iface; admit = _52_225.admit; lax = _52_225.lax; type_of = _52_225.type_of; universe_of = _52_225.universe_of; use_bv_sorts = _52_225.use_bv_sorts}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _143_525 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _143_525)))


let new_u_univ = (fun _52_234 -> (let _143_527 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_143_527)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _52_247) -> begin
(

let _52_249 = ()
in (

let n = ((FStar_List.length formals) - 1)
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _143_534 = (FStar_Syntax_Subst.subst vs t)
in (us, _143_534)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_262 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_270 -> (match (_52_270) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_273 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _143_550 = (let _143_549 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _143_548 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _143_547 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _143_546 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _143_549 _143_548 _143_547 _143_546)))))
in (FStar_All.failwith _143_550))
end else begin
()
end
in (let _143_551 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _143_551))))
end
| _52_276 -> begin
(let _143_553 = (let _143_552 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _143_552))
in (FStar_All.failwith _143_553))
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

let rec aux = (fun c l -> (match ((c, l)) with
| ([], _52_287) -> begin
Maybe
end
| (_52_290, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_301 -> begin
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

let _52_307 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _143_573 = (let _143_572 = (inst_tscheme t)
in FStar_Util.Inl (_143_572))
in Some (_143_573))
end else begin
None
end
end
| Binding_sig (_52_316, FStar_Syntax_Syntax.Sig_bundle (ses, _52_319, _52_321, _52_323)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _143_575 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _143_575 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_336) -> begin
Some (t)
end
| _52_339 -> begin
(cache t)
end))
in if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
(maybe_cache (FStar_Util.Inr ((s, None))))
end else begin
None
end)
end
| Binding_sig_inst (lids, s, us) -> begin
if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
Some (FStar_Util.Inr ((s, Some (us))))
end else begin
None
end
end
| _52_346 -> begin
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
Some (FStar_Util.Inr ((se, None)))
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
| Some (_52_356) -> begin
true
end))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_362, _52_364, _52_366) -> begin
(add_sigelts env ses)
end
| _52_370 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_3 -> (match (_52_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_381 -> begin
None
end))))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_4 -> (match (_52_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_388 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_392, (lb)::[]), _52_397, _52_399, _52_401) -> begin
(let _143_608 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_143_608))
end
| FStar_Syntax_Syntax.Sig_let ((_52_405, lbs), _52_409, _52_411, _52_413) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_418) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _143_610 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_143_610))
end else begin
None
end
end)))
end
| _52_423 -> begin
None
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _143_618 = (let _143_617 = (let _143_616 = (variable_not_found bv)
in (let _143_615 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_143_616, _143_615)))
in FStar_Syntax_Syntax.Error (_143_617))
in (Prims.raise _143_618))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_432) -> begin
(let _143_624 = (let _143_623 = (let _143_622 = (let _143_621 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _143_621))
in (ne.FStar_Syntax_Syntax.univs, _143_622))
in (inst_tscheme _143_623))
in Some (_143_624))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_439, _52_441, _52_443) -> begin
(let _143_628 = (let _143_627 = (let _143_626 = (let _143_625 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _143_625))
in (us, _143_626))
in (inst_tscheme _143_627))
in Some (_143_628))
end
| _52_447 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_457, t) -> begin
Some (t)
end)
end
| _52_462 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (

let mapper = (fun _52_5 -> (match (_52_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_469, uvs, t, _52_473, _52_475, _52_477, _52_479, _52_481), None) -> begin
(let _143_639 = (inst_tscheme (uvs, t))
in Some (_143_639))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_492), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _143_640 = (inst_tscheme (uvs, t))
in Some (_143_640))
end else begin
None
end
end else begin
(let _143_641 = (inst_tscheme (uvs, t))
in Some (_143_641))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_503, _52_505, _52_507, _52_509), None) -> begin
(match (tps) with
| [] -> begin
(let _143_643 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _143_642 -> Some (_143_642)) _143_643))
end
| _52_517 -> begin
(let _143_648 = (let _143_647 = (let _143_646 = (let _143_645 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _143_645))
in (uvs, _143_646))
in (inst_tscheme _143_647))
in (FStar_All.pipe_left (fun _143_644 -> Some (_143_644)) _143_648))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_523, _52_525, _52_527, _52_529), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _143_650 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _143_649 -> Some (_143_649)) _143_650))
end
| _52_538 -> begin
(let _143_655 = (let _143_654 = (let _143_653 = (let _143_652 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _143_652))
in (uvs, _143_653))
in (inst_tscheme_with _143_654 us))
in (FStar_All.pipe_left (fun _143_651 -> Some (_143_651)) _143_655))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_542), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_547 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _143_656 = (lookup_qname env lid)
in (FStar_Util.bind_opt _143_656 mapper))) with
| Some (us, t) -> begin
Some ((us, (

let _52_553 = t
in {FStar_Syntax_Syntax.n = _52_553.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_553.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_553.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_6 -> (match (_52_6) with
| FStar_Util.Inl (_52_560) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_564) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_568, _52_570, _52_572, qs, _52_575) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_579) -> begin
Some (true)
end
| _52_582 -> begin
Some (false)
end)
end))
in (match ((let _143_663 = (lookup_qname env lid)
in (FStar_Util.bind_opt _143_663 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _143_670 = (let _143_669 = (let _143_668 = (name_not_found l)
in (_143_668, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_143_669))
in (Prims.raise _143_670))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_595, uvs, t, _52_599, _52_601), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_609 -> begin
(let _143_677 = (let _143_676 = (let _143_675 = (name_not_found lid)
in (_143_675, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_143_676))
in (Prims.raise _143_677))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_613, uvs, t, _52_617, _52_619, _52_621, _52_623, _52_625), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_633 -> begin
(let _143_684 = (let _143_683 = (let _143_682 = (name_not_found lid)
in (_143_682, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_143_683))
in (Prims.raise _143_684))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_643, lbs), _52_647, _52_649, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _143_693 = (let _143_692 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _143_692))
in Some (_143_693))
end else begin
None
end)))
end
| _52_656 -> begin
None
end)
end
| _52_658 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _143_700 = (let _143_699 = (let _143_698 = (name_not_found ftv)
in (_143_698, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_143_699))
in (Prims.raise _143_700))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_668 -> (match (()) with
| () -> begin
(let _143_711 = (let _143_710 = (FStar_Util.string_of_int i)
in (let _143_709 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _143_710 _143_709)))
in (FStar_All.failwith _143_711))
end))
in (

let _52_672 = (lookup_datacon env lid)
in (match (_52_672) with
| (_52_670, t) -> begin
(match ((let _143_712 = (FStar_Syntax_Subst.compress t)
in _143_712.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_675) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _143_713 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _143_713 Prims.fst)))
end
end
| _52_680 -> begin
(fail ())
end)
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_684, uvs, t, q, _52_689), None)) -> begin
Some (((uvs, t), q))
end
| _52_697 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_707), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_717 -> begin
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
in (match ((binders, univs)) with
| ([], _52_721) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_724, (_52_731)::(_52_728)::_52_726) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _143_727 = (let _143_726 = (FStar_Syntax_Print.lid_to_string lid)
in (let _143_725 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _143_726 _143_725)))
in (FStar_All.failwith _143_727))
end
| _52_735 -> begin
(

let _52_739 = (let _143_729 = (let _143_728 = (FStar_Syntax_Util.arrow binders c)
in (univs, _143_728))
in (inst_tscheme_with _143_729 insts))
in (match (_52_739) with
| (_52_737, t) -> begin
(match ((let _143_730 = (FStar_Syntax_Subst.compress t)
in _143_730.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _52_745 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_747 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create 20)
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_755, c) -> begin
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

let _52_769 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_775, _52_777, _52_779, _52_781, _52_783, dcs, _52_786, _52_788), _52_792)) -> begin
dcs
end
| _52_797 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_801, _52_803, _52_805, l, _52_808, _52_810, _52_812, _52_814), _52_818)) -> begin
l
end
| _52_823 -> begin
(let _143_746 = (let _143_745 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _143_745))
in (FStar_All.failwith _143_746))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_827, _52_829, _52_831, _52_833, _52_835, _52_837, _52_839, _52_841), _52_845)) -> begin
true
end
| _52_850 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_854, _52_856, _52_858, _52_860, _52_862, _52_864, tags, _52_867), _52_871)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_883 -> begin
false
end)) tags)
end
| _52_885 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_889, _52_891, _52_893, quals, _52_896), _52_900)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_906) -> begin
true
end
| _52_909 -> begin
false
end)) quals)
end
| _52_911 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _143_765 = (FStar_Syntax_Util.un_uinst head)
in _143_765.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_917 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _143_777 = (let _143_776 = (let _143_775 = (name_not_found l)
in (_143_775, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_143_776))
in (Prims.raise _143_777))
end
| Some (md) -> begin
md
end))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_945 -> (match (_52_945) with
| (m1, m2, _52_940, _52_942, _52_944) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _143_853 = (let _143_852 = (let _143_851 = (let _143_850 = (FStar_Syntax_Print.lid_to_string l1)
in (let _143_849 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _143_850 _143_849)))
in (_143_851, env.range))
in FStar_Syntax_Syntax.Error (_143_852))
in (Prims.raise _143_853))
end
| Some (_52_948, _52_950, m3, j1, j2) -> begin
(m3, j1, j2)
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
(let _143_868 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _143_868))
end
| Some (md) -> begin
(

let _52_971 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_52_971) with
| (_52_969, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_980))::((wp, _52_976))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _52_988 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_995) -> begin
(

let effects = (

let _52_998 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_998.order; joins = _52_998.joins})
in (

let _52_1001 = env
in {solver = _52_1001.solver; range = _52_1001.range; curmodule = _52_1001.curmodule; gamma = _52_1001.gamma; gamma_cache = _52_1001.gamma_cache; modules = _52_1001.modules; expected_typ = _52_1001.expected_typ; sigtab = _52_1001.sigtab; is_pattern = _52_1001.is_pattern; instantiate_imp = _52_1001.instantiate_imp; effects = effects; generalize = _52_1001.generalize; letrecs = _52_1001.letrecs; top_level = _52_1001.top_level; check_uvars = _52_1001.check_uvars; use_eq = _52_1001.use_eq; is_iface = _52_1001.is_iface; admit = _52_1001.admit; lax = _52_1001.lax; type_of = _52_1001.type_of; universe_of = _52_1001.universe_of; use_bv_sorts = _52_1001.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1005) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _143_883 = (e1.mlift r wp1)
in (e2.mlift r _143_883)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1020 = (inst_tscheme lift_t)
in (match (_52_1020) with
| (_52_1018, lift_t) -> begin
(let _143_895 = (let _143_894 = (let _143_893 = (let _143_892 = (FStar_Syntax_Syntax.as_arg r)
in (let _143_891 = (let _143_890 = (FStar_Syntax_Syntax.as_arg wp1)
in (_143_890)::[])
in (_143_892)::_143_891))
in (lift_t, _143_893))
in FStar_Syntax_Syntax.Tm_app (_143_894))
in (FStar_Syntax_Syntax.mk _143_895 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _143_912 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _143_912 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _143_913 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _143_913 FStar_Syntax_Syntax.Delta_constant None))
in (let _143_914 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _143_914)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1037 -> (match (_52_1037) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _143_920 -> Some (_143_920)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _143_928 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _143_927 = (find_edge order (i, k))
in (let _143_926 = (find_edge order (k, j))
in (_143_927, _143_926)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1049 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _143_928))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _143_1020 = (find_edge order (i, k))
in (let _143_1019 = (find_edge order (j, k))
in (_143_1020, _143_1019)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _52_1066, _52_1068) -> begin
if ((let _143_1021 = (find_edge order (k, ub))
in (FStar_Util.is_some _143_1021)) && (not ((let _143_1022 = (find_edge order (ub, k))
in (FStar_Util.is_some _143_1022))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _52_1072 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (

let effects = (

let _52_1081 = env.effects
in {decls = _52_1081.decls; order = order; joins = joins})
in (

let _52_1084 = env
in {solver = _52_1084.solver; range = _52_1084.range; curmodule = _52_1084.curmodule; gamma = _52_1084.gamma; gamma_cache = _52_1084.gamma_cache; modules = _52_1084.modules; expected_typ = _52_1084.expected_typ; sigtab = _52_1084.sigtab; is_pattern = _52_1084.is_pattern; instantiate_imp = _52_1084.instantiate_imp; effects = effects; generalize = _52_1084.generalize; letrecs = _52_1084.letrecs; top_level = _52_1084.top_level; check_uvars = _52_1084.check_uvars; use_eq = _52_1084.use_eq; is_iface = _52_1084.is_iface; admit = _52_1084.admit; lax = _52_1084.lax; type_of = _52_1084.type_of; universe_of = _52_1084.universe_of; use_bv_sorts = _52_1084.use_bv_sorts})))))))))))))
end
| _52_1087 -> begin
env
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _143_1071 = (

let _52_1090 = env
in (let _143_1070 = (let _143_1069 = (let _143_1068 = (let _143_1067 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_143_1067, s))
in Binding_sig (_143_1068))
in (_143_1069)::env.gamma)
in {solver = _52_1090.solver; range = _52_1090.range; curmodule = _52_1090.curmodule; gamma = _143_1070; gamma_cache = _52_1090.gamma_cache; modules = _52_1090.modules; expected_typ = _52_1090.expected_typ; sigtab = _52_1090.sigtab; is_pattern = _52_1090.is_pattern; instantiate_imp = _52_1090.instantiate_imp; effects = _52_1090.effects; generalize = _52_1090.generalize; letrecs = _52_1090.letrecs; top_level = _52_1090.top_level; check_uvars = _52_1090.check_uvars; use_eq = _52_1090.use_eq; is_iface = _52_1090.is_iface; admit = _52_1090.admit; lax = _52_1090.lax; type_of = _52_1090.type_of; universe_of = _52_1090.universe_of; use_bv_sorts = _52_1090.use_bv_sorts}))
in (build_lattice _143_1071 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _143_1082 = (

let _52_1095 = env
in (let _143_1081 = (let _143_1080 = (let _143_1079 = (let _143_1078 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_143_1078, s, us))
in Binding_sig_inst (_143_1079))
in (_143_1080)::env.gamma)
in {solver = _52_1095.solver; range = _52_1095.range; curmodule = _52_1095.curmodule; gamma = _143_1081; gamma_cache = _52_1095.gamma_cache; modules = _52_1095.modules; expected_typ = _52_1095.expected_typ; sigtab = _52_1095.sigtab; is_pattern = _52_1095.is_pattern; instantiate_imp = _52_1095.instantiate_imp; effects = _52_1095.effects; generalize = _52_1095.generalize; letrecs = _52_1095.letrecs; top_level = _52_1095.top_level; check_uvars = _52_1095.check_uvars; use_eq = _52_1095.use_eq; is_iface = _52_1095.is_iface; admit = _52_1095.admit; lax = _52_1095.lax; type_of = _52_1095.type_of; universe_of = _52_1095.universe_of; use_bv_sorts = _52_1095.use_bv_sorts}))
in (build_lattice _143_1082 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1099 = env
in {solver = _52_1099.solver; range = _52_1099.range; curmodule = _52_1099.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1099.gamma_cache; modules = _52_1099.modules; expected_typ = _52_1099.expected_typ; sigtab = _52_1099.sigtab; is_pattern = _52_1099.is_pattern; instantiate_imp = _52_1099.instantiate_imp; effects = _52_1099.effects; generalize = _52_1099.generalize; letrecs = _52_1099.letrecs; top_level = _52_1099.top_level; check_uvars = _52_1099.check_uvars; use_eq = _52_1099.use_eq; is_iface = _52_1099.is_iface; admit = _52_1099.admit; lax = _52_1099.lax; type_of = _52_1099.type_of; universe_of = _52_1099.universe_of; use_bv_sorts = _52_1099.use_bv_sorts}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1109 -> (match (_52_1109) with
| (x, _52_1108) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1114 = ()
in (

let x = (

let _52_1116 = x
in {FStar_Syntax_Syntax.ppname = _52_1116.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1116.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1126 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1128 = env
in {solver = _52_1128.solver; range = _52_1128.range; curmodule = _52_1128.curmodule; gamma = []; gamma_cache = _52_1128.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1128.sigtab; is_pattern = _52_1128.is_pattern; instantiate_imp = _52_1128.instantiate_imp; effects = _52_1128.effects; generalize = _52_1128.generalize; letrecs = _52_1128.letrecs; top_level = _52_1128.top_level; check_uvars = _52_1128.check_uvars; use_eq = _52_1128.use_eq; is_iface = _52_1128.is_iface; admit = _52_1128.admit; lax = _52_1128.lax; type_of = _52_1128.type_of; universe_of = _52_1128.universe_of; use_bv_sorts = _52_1128.use_bv_sorts})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1136 = env
in {solver = _52_1136.solver; range = _52_1136.range; curmodule = _52_1136.curmodule; gamma = _52_1136.gamma; gamma_cache = _52_1136.gamma_cache; modules = _52_1136.modules; expected_typ = Some (t); sigtab = _52_1136.sigtab; is_pattern = _52_1136.is_pattern; instantiate_imp = _52_1136.instantiate_imp; effects = _52_1136.effects; generalize = _52_1136.generalize; letrecs = _52_1136.letrecs; top_level = _52_1136.top_level; check_uvars = _52_1136.check_uvars; use_eq = false; is_iface = _52_1136.is_iface; admit = _52_1136.admit; lax = _52_1136.lax; type_of = _52_1136.type_of; universe_of = _52_1136.universe_of; use_bv_sorts = _52_1136.use_bv_sorts}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _143_1125 = (expected_typ env)
in ((

let _52_1143 = env
in {solver = _52_1143.solver; range = _52_1143.range; curmodule = _52_1143.curmodule; gamma = _52_1143.gamma; gamma_cache = _52_1143.gamma_cache; modules = _52_1143.modules; expected_typ = None; sigtab = _52_1143.sigtab; is_pattern = _52_1143.is_pattern; instantiate_imp = _52_1143.instantiate_imp; effects = _52_1143.effects; generalize = _52_1143.generalize; letrecs = _52_1143.letrecs; top_level = _52_1143.top_level; check_uvars = _52_1143.check_uvars; use_eq = false; is_iface = _52_1143.is_iface; admit = _52_1143.admit; lax = _52_1143.lax; type_of = _52_1143.type_of; universe_of = _52_1143.universe_of; use_bv_sorts = _52_1143.use_bv_sorts}), _143_1125)))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _143_1131 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1150, se) -> begin
(se)::[]
end
| _52_1155 -> begin
[]
end))))
in (FStar_All.pipe_right _143_1131 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1157 = (add_sigelts env sigs)
in (

let _52_1159 = env
in {solver = _52_1159.solver; range = _52_1159.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1159.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1159.expected_typ; sigtab = _52_1159.sigtab; is_pattern = _52_1159.is_pattern; instantiate_imp = _52_1159.instantiate_imp; effects = _52_1159.effects; generalize = _52_1159.generalize; letrecs = _52_1159.letrecs; top_level = _52_1159.top_level; check_uvars = _52_1159.check_uvars; use_eq = _52_1159.use_eq; is_iface = _52_1159.is_iface; admit = _52_1159.admit; lax = _52_1159.lax; type_of = _52_1159.type_of; universe_of = _52_1159.universe_of; use_bv_sorts = _52_1159.use_bv_sorts})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1172))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _143_1143 = (let _143_1142 = (FStar_Syntax_Free.uvars t)
in (ext out _143_1142))
in (aux _143_1143 tl))
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
(let _143_1155 = (let _143_1154 = (FStar_Syntax_Free.univs t)
in (ext out _143_1154))
in (aux _143_1155 tl))
end
| (Binding_sig (_52_1242))::_52_1240 -> begin
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


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _143_1162 = (let _143_1161 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _143_1161 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _143_1162 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1274) -> begin
(FStar_List.append lids keys)
end
| _52_1278 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1280 v keys -> (let _143_1185 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _143_1185 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1284 -> ()); push = (fun _52_1286 -> ()); pop = (fun _52_1288 -> ()); mark = (fun _52_1290 -> ()); reset_mark = (fun _52_1292 -> ()); commit_mark = (fun _52_1294 -> ()); encode_modul = (fun _52_1296 _52_1298 -> ()); encode_sig = (fun _52_1300 _52_1302 -> ()); solve = (fun _52_1304 _52_1306 _52_1308 -> ()); is_trivial = (fun _52_1310 _52_1312 -> false); finish = (fun _52_1314 -> ()); refresh = (fun _52_1315 -> ())}


let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _143_1221 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _143_1221)))




