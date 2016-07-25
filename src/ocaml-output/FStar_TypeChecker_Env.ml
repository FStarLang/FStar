
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


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _143_424 = (new_gamma_cache ())
in (let _143_423 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _143_424; modules = []; expected_typ = None; sigtab = _143_423; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _52_175 = (let _143_478 = (let _143_477 = (FStar_ST.read stack)
in (env)::_143_477)
in (FStar_ST.op_Colon_Equals stack _143_478))
in (

let _52_177 = env
in (let _143_480 = (FStar_Util.smap_copy (gamma_cache env))
in (let _143_479 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_177.solver; range = _52_177.range; curmodule = _52_177.curmodule; gamma = _52_177.gamma; gamma_cache = _143_480; modules = _52_177.modules; expected_typ = _52_177.expected_typ; sigtab = _143_479; is_pattern = _52_177.is_pattern; instantiate_imp = _52_177.instantiate_imp; effects = _52_177.effects; generalize = _52_177.generalize; letrecs = _52_177.letrecs; top_level = _52_177.top_level; check_uvars = _52_177.check_uvars; use_eq = _52_177.use_eq; is_iface = _52_177.is_iface; admit = _52_177.admit; lax = _52_177.lax; type_of = _52_177.type_of; universe_of = _52_177.universe_of; use_bv_sorts = _52_177.use_bv_sorts})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_184 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_187 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let mark = (fun env -> (push env))
in (

let commit_mark = (fun env -> (

let _52_192 = (let _143_487 = (pop env)
in (Prims.ignore _143_487))
in env))
in (

let reset_mark = (fun env -> (pop env))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop}))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_198 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_201 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_204 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_207 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_211 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_217 = e
in {solver = _52_217.solver; range = r; curmodule = _52_217.curmodule; gamma = _52_217.gamma; gamma_cache = _52_217.gamma_cache; modules = _52_217.modules; expected_typ = _52_217.expected_typ; sigtab = _52_217.sigtab; is_pattern = _52_217.is_pattern; instantiate_imp = _52_217.instantiate_imp; effects = _52_217.effects; generalize = _52_217.generalize; letrecs = _52_217.letrecs; top_level = _52_217.top_level; check_uvars = _52_217.check_uvars; use_eq = _52_217.use_eq; is_iface = _52_217.is_iface; admit = _52_217.admit; lax = _52_217.lax; type_of = _52_217.type_of; universe_of = _52_217.universe_of; use_bv_sorts = _52_217.use_bv_sorts})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_224 = env
in {solver = _52_224.solver; range = _52_224.range; curmodule = lid; gamma = _52_224.gamma; gamma_cache = _52_224.gamma_cache; modules = _52_224.modules; expected_typ = _52_224.expected_typ; sigtab = _52_224.sigtab; is_pattern = _52_224.is_pattern; instantiate_imp = _52_224.instantiate_imp; effects = _52_224.effects; generalize = _52_224.generalize; letrecs = _52_224.letrecs; top_level = _52_224.top_level; check_uvars = _52_224.check_uvars; use_eq = _52_224.use_eq; is_iface = _52_224.is_iface; admit = _52_224.admit; lax = _52_224.lax; type_of = _52_224.type_of; universe_of = _52_224.universe_of; use_bv_sorts = _52_224.use_bv_sorts}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _143_535 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _143_535)))


let new_u_univ = (fun _52_233 -> (let _143_537 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_143_537)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _52_246) -> begin
(

let _52_248 = ()
in (

let n = ((FStar_List.length formals) - 1)
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _143_544 = (FStar_Syntax_Subst.subst vs t)
in (us, _143_544)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_261 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_269 -> (match (_52_269) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_272 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _143_560 = (let _143_559 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _143_558 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _143_557 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _143_556 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _143_559 _143_558 _143_557 _143_556)))))
in (FStar_All.failwith _143_560))
end else begin
()
end
in (let _143_561 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _143_561))))
end
| _52_275 -> begin
(let _143_563 = (let _143_562 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _143_562))
in (FStar_All.failwith _143_563))
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
| ([], _52_286) -> begin
Maybe
end
| (_52_289, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_300 -> begin
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

let _52_306 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _143_583 = (let _143_582 = (inst_tscheme t)
in FStar_Util.Inl (_143_582))
in Some (_143_583))
end else begin
None
end
end
| Binding_sig (_52_315, FStar_Syntax_Syntax.Sig_bundle (ses, _52_318, _52_320, _52_322)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _143_585 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _143_585 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_335) -> begin
Some (t)
end
| _52_338 -> begin
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
| _52_345 -> begin
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
| Some (_52_355) -> begin
true
end))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_361, _52_363, _52_365) -> begin
(add_sigelts env ses)
end
| _52_369 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_3 -> (match (_52_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_380 -> begin
None
end))))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_4 -> (match (_52_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_387 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_391, (lb)::[]), _52_396, _52_398, _52_400) -> begin
(let _143_618 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_143_618))
end
| FStar_Syntax_Syntax.Sig_let ((_52_404, lbs), _52_408, _52_410, _52_412) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_417) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _143_620 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_143_620))
end else begin
None
end
end)))
end
| _52_422 -> begin
None
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _143_628 = (let _143_627 = (let _143_626 = (variable_not_found bv)
in (let _143_625 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_143_626, _143_625)))
in FStar_Syntax_Syntax.Error (_143_627))
in (Prims.raise _143_628))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_431) -> begin
(let _143_634 = (let _143_633 = (let _143_632 = (let _143_631 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _143_631))
in (ne.FStar_Syntax_Syntax.univs, _143_632))
in (inst_tscheme _143_633))
in Some (_143_634))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_438, _52_440, _52_442) -> begin
(let _143_638 = (let _143_637 = (let _143_636 = (let _143_635 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _143_635))
in (us, _143_636))
in (inst_tscheme _143_637))
in Some (_143_638))
end
| _52_446 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_456, t) -> begin
Some (t)
end)
end
| _52_461 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (

let mapper = (fun _52_5 -> (match (_52_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_468, uvs, t, _52_472, _52_474, _52_476, _52_478, _52_480), None) -> begin
(let _143_649 = (inst_tscheme (uvs, t))
in Some (_143_649))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_491), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _143_650 = (inst_tscheme (uvs, t))
in Some (_143_650))
end else begin
None
end
end else begin
(let _143_651 = (inst_tscheme (uvs, t))
in Some (_143_651))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_502, _52_504, _52_506, _52_508), None) -> begin
(match (tps) with
| [] -> begin
(let _143_653 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _143_652 -> Some (_143_652)) _143_653))
end
| _52_516 -> begin
(let _143_658 = (let _143_657 = (let _143_656 = (let _143_655 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _143_655))
in (uvs, _143_656))
in (inst_tscheme _143_657))
in (FStar_All.pipe_left (fun _143_654 -> Some (_143_654)) _143_658))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_522, _52_524, _52_526, _52_528), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _143_660 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _143_659 -> Some (_143_659)) _143_660))
end
| _52_537 -> begin
(let _143_665 = (let _143_664 = (let _143_663 = (let _143_662 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _143_662))
in (uvs, _143_663))
in (inst_tscheme_with _143_664 us))
in (FStar_All.pipe_left (fun _143_661 -> Some (_143_661)) _143_665))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_541), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_546 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _143_666 = (lookup_qname env lid)
in (FStar_Util.bind_opt _143_666 mapper))) with
| Some (us, t) -> begin
Some ((us, (

let _52_552 = t
in {FStar_Syntax_Syntax.n = _52_552.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_552.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_552.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_6 -> (match (_52_6) with
| FStar_Util.Inl (_52_559) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_563) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_567, _52_569, _52_571, qs, _52_574) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_578) -> begin
Some (true)
end
| _52_581 -> begin
Some (false)
end)
end))
in (match ((let _143_673 = (lookup_qname env lid)
in (FStar_Util.bind_opt _143_673 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _143_680 = (let _143_679 = (let _143_678 = (name_not_found l)
in (_143_678, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_143_679))
in (Prims.raise _143_680))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_594, uvs, t, _52_598, _52_600), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_608 -> begin
(let _143_687 = (let _143_686 = (let _143_685 = (name_not_found lid)
in (_143_685, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_143_686))
in (Prims.raise _143_687))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_612, uvs, t, _52_616, _52_618, _52_620, _52_622, _52_624), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_632 -> begin
(let _143_694 = (let _143_693 = (let _143_692 = (name_not_found lid)
in (_143_692, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_143_693))
in (Prims.raise _143_694))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_642, lbs), _52_646, _52_648, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _143_703 = (let _143_702 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _143_702))
in Some (_143_703))
end else begin
None
end)))
end
| _52_655 -> begin
None
end)
end
| _52_657 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _143_710 = (let _143_709 = (let _143_708 = (name_not_found ftv)
in (_143_708, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_143_709))
in (Prims.raise _143_710))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_667 -> (match (()) with
| () -> begin
(let _143_721 = (let _143_720 = (FStar_Util.string_of_int i)
in (let _143_719 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _143_720 _143_719)))
in (FStar_All.failwith _143_721))
end))
in (

let _52_671 = (lookup_datacon env lid)
in (match (_52_671) with
| (_52_669, t) -> begin
(match ((let _143_722 = (FStar_Syntax_Subst.compress t)
in _143_722.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_674) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _143_723 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _143_723 Prims.fst)))
end
end
| _52_679 -> begin
(fail ())
end)
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_683, uvs, t, q, _52_688), None)) -> begin
Some (((uvs, t), q))
end
| _52_696 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_706), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_716 -> begin
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
| ([], _52_720) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_723, (_52_730)::(_52_727)::_52_725) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _143_737 = (let _143_736 = (FStar_Syntax_Print.lid_to_string lid)
in (let _143_735 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _143_736 _143_735)))
in (FStar_All.failwith _143_737))
end
| _52_734 -> begin
(

let _52_738 = (let _143_739 = (let _143_738 = (FStar_Syntax_Util.arrow binders c)
in (univs, _143_738))
in (inst_tscheme_with _143_739 insts))
in (match (_52_738) with
| (_52_736, t) -> begin
(match ((let _143_740 = (FStar_Syntax_Subst.compress t)
in _143_740.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _52_744 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_746 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create 20)
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_754, c) -> begin
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

let _52_768 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_774, _52_776, _52_778, _52_780, _52_782, dcs, _52_785, _52_787), _52_791)) -> begin
dcs
end
| _52_796 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_800, _52_802, _52_804, l, _52_807, _52_809, _52_811, _52_813), _52_817)) -> begin
l
end
| _52_822 -> begin
(let _143_756 = (let _143_755 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _143_755))
in (FStar_All.failwith _143_756))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_826, _52_828, _52_830, _52_832, _52_834, _52_836, _52_838, _52_840), _52_844)) -> begin
true
end
| _52_849 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_853, _52_855, _52_857, _52_859, _52_861, _52_863, tags, _52_866), _52_870)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_882 -> begin
false
end)) tags)
end
| _52_884 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_888, _52_890, _52_892, quals, _52_895), _52_899)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_905) -> begin
true
end
| _52_908 -> begin
false
end)) quals)
end
| _52_910 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _143_775 = (FStar_Syntax_Util.un_uinst head)
in _143_775.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_916 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _143_787 = (let _143_786 = (let _143_785 = (name_not_found l)
in (_143_785, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_143_786))
in (Prims.raise _143_787))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_944 -> (match (_52_944) with
| (m1, m2, _52_939, _52_941, _52_943) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _143_863 = (let _143_862 = (let _143_861 = (let _143_860 = (FStar_Syntax_Print.lid_to_string l1)
in (let _143_859 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _143_860 _143_859)))
in (_143_861, env.range))
in FStar_Syntax_Syntax.Error (_143_862))
in (Prims.raise _143_863))
end
| Some (_52_947, _52_949, m3, j1, j2) -> begin
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
(let _143_878 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _143_878))
end
| Some (md) -> begin
(

let _52_970 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_52_970) with
| (_52_968, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_979))::((wp, _52_975))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _52_987 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_994) -> begin
(

let effects = (

let _52_997 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_997.order; joins = _52_997.joins})
in (

let _52_1000 = env
in {solver = _52_1000.solver; range = _52_1000.range; curmodule = _52_1000.curmodule; gamma = _52_1000.gamma; gamma_cache = _52_1000.gamma_cache; modules = _52_1000.modules; expected_typ = _52_1000.expected_typ; sigtab = _52_1000.sigtab; is_pattern = _52_1000.is_pattern; instantiate_imp = _52_1000.instantiate_imp; effects = effects; generalize = _52_1000.generalize; letrecs = _52_1000.letrecs; top_level = _52_1000.top_level; check_uvars = _52_1000.check_uvars; use_eq = _52_1000.use_eq; is_iface = _52_1000.is_iface; admit = _52_1000.admit; lax = _52_1000.lax; type_of = _52_1000.type_of; universe_of = _52_1000.universe_of; use_bv_sorts = _52_1000.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1004) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _143_893 = (e1.mlift r wp1)
in (e2.mlift r _143_893)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1019 = (inst_tscheme lift_t)
in (match (_52_1019) with
| (_52_1017, lift_t) -> begin
(let _143_905 = (let _143_904 = (let _143_903 = (let _143_902 = (FStar_Syntax_Syntax.as_arg r)
in (let _143_901 = (let _143_900 = (FStar_Syntax_Syntax.as_arg wp1)
in (_143_900)::[])
in (_143_902)::_143_901))
in (lift_t, _143_903))
in FStar_Syntax_Syntax.Tm_app (_143_904))
in (FStar_Syntax_Syntax.mk _143_905 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _143_922 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _143_922 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _143_923 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _143_923 FStar_Syntax_Syntax.Delta_constant None))
in (let _143_924 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _143_924)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1036 -> (match (_52_1036) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _143_930 -> Some (_143_930)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _143_938 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _143_937 = (find_edge order (i, k))
in (let _143_936 = (find_edge order (k, j))
in (_143_937, _143_936)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1048 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _143_938))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _143_1030 = (find_edge order (i, k))
in (let _143_1029 = (find_edge order (j, k))
in (_143_1030, _143_1029)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _52_1065, _52_1067) -> begin
if ((let _143_1031 = (find_edge order (k, ub))
in (FStar_Util.is_some _143_1031)) && (not ((let _143_1032 = (find_edge order (ub, k))
in (FStar_Util.is_some _143_1032))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _52_1071 -> begin
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

let _52_1080 = env.effects
in {decls = _52_1080.decls; order = order; joins = joins})
in (

let _52_1083 = env
in {solver = _52_1083.solver; range = _52_1083.range; curmodule = _52_1083.curmodule; gamma = _52_1083.gamma; gamma_cache = _52_1083.gamma_cache; modules = _52_1083.modules; expected_typ = _52_1083.expected_typ; sigtab = _52_1083.sigtab; is_pattern = _52_1083.is_pattern; instantiate_imp = _52_1083.instantiate_imp; effects = effects; generalize = _52_1083.generalize; letrecs = _52_1083.letrecs; top_level = _52_1083.top_level; check_uvars = _52_1083.check_uvars; use_eq = _52_1083.use_eq; is_iface = _52_1083.is_iface; admit = _52_1083.admit; lax = _52_1083.lax; type_of = _52_1083.type_of; universe_of = _52_1083.universe_of; use_bv_sorts = _52_1083.use_bv_sorts})))))))))))))
end
| _52_1086 -> begin
env
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _143_1081 = (

let _52_1089 = env
in (let _143_1080 = (let _143_1079 = (let _143_1078 = (let _143_1077 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_143_1077, s))
in Binding_sig (_143_1078))
in (_143_1079)::env.gamma)
in {solver = _52_1089.solver; range = _52_1089.range; curmodule = _52_1089.curmodule; gamma = _143_1080; gamma_cache = _52_1089.gamma_cache; modules = _52_1089.modules; expected_typ = _52_1089.expected_typ; sigtab = _52_1089.sigtab; is_pattern = _52_1089.is_pattern; instantiate_imp = _52_1089.instantiate_imp; effects = _52_1089.effects; generalize = _52_1089.generalize; letrecs = _52_1089.letrecs; top_level = _52_1089.top_level; check_uvars = _52_1089.check_uvars; use_eq = _52_1089.use_eq; is_iface = _52_1089.is_iface; admit = _52_1089.admit; lax = _52_1089.lax; type_of = _52_1089.type_of; universe_of = _52_1089.universe_of; use_bv_sorts = _52_1089.use_bv_sorts}))
in (build_lattice _143_1081 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _143_1092 = (

let _52_1094 = env
in (let _143_1091 = (let _143_1090 = (let _143_1089 = (let _143_1088 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_143_1088, s, us))
in Binding_sig_inst (_143_1089))
in (_143_1090)::env.gamma)
in {solver = _52_1094.solver; range = _52_1094.range; curmodule = _52_1094.curmodule; gamma = _143_1091; gamma_cache = _52_1094.gamma_cache; modules = _52_1094.modules; expected_typ = _52_1094.expected_typ; sigtab = _52_1094.sigtab; is_pattern = _52_1094.is_pattern; instantiate_imp = _52_1094.instantiate_imp; effects = _52_1094.effects; generalize = _52_1094.generalize; letrecs = _52_1094.letrecs; top_level = _52_1094.top_level; check_uvars = _52_1094.check_uvars; use_eq = _52_1094.use_eq; is_iface = _52_1094.is_iface; admit = _52_1094.admit; lax = _52_1094.lax; type_of = _52_1094.type_of; universe_of = _52_1094.universe_of; use_bv_sorts = _52_1094.use_bv_sorts}))
in (build_lattice _143_1092 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1098 = env
in {solver = _52_1098.solver; range = _52_1098.range; curmodule = _52_1098.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1098.gamma_cache; modules = _52_1098.modules; expected_typ = _52_1098.expected_typ; sigtab = _52_1098.sigtab; is_pattern = _52_1098.is_pattern; instantiate_imp = _52_1098.instantiate_imp; effects = _52_1098.effects; generalize = _52_1098.generalize; letrecs = _52_1098.letrecs; top_level = _52_1098.top_level; check_uvars = _52_1098.check_uvars; use_eq = _52_1098.use_eq; is_iface = _52_1098.is_iface; admit = _52_1098.admit; lax = _52_1098.lax; type_of = _52_1098.type_of; universe_of = _52_1098.universe_of; use_bv_sorts = _52_1098.use_bv_sorts}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1108 -> (match (_52_1108) with
| (x, _52_1107) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1113 = ()
in (

let x = (

let _52_1115 = x
in {FStar_Syntax_Syntax.ppname = _52_1115.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1115.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1125 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1127 = env
in {solver = _52_1127.solver; range = _52_1127.range; curmodule = _52_1127.curmodule; gamma = []; gamma_cache = _52_1127.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1127.sigtab; is_pattern = _52_1127.is_pattern; instantiate_imp = _52_1127.instantiate_imp; effects = _52_1127.effects; generalize = _52_1127.generalize; letrecs = _52_1127.letrecs; top_level = _52_1127.top_level; check_uvars = _52_1127.check_uvars; use_eq = _52_1127.use_eq; is_iface = _52_1127.is_iface; admit = _52_1127.admit; lax = _52_1127.lax; type_of = _52_1127.type_of; universe_of = _52_1127.universe_of; use_bv_sorts = _52_1127.use_bv_sorts})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1135 = env
in {solver = _52_1135.solver; range = _52_1135.range; curmodule = _52_1135.curmodule; gamma = _52_1135.gamma; gamma_cache = _52_1135.gamma_cache; modules = _52_1135.modules; expected_typ = Some (t); sigtab = _52_1135.sigtab; is_pattern = _52_1135.is_pattern; instantiate_imp = _52_1135.instantiate_imp; effects = _52_1135.effects; generalize = _52_1135.generalize; letrecs = _52_1135.letrecs; top_level = _52_1135.top_level; check_uvars = _52_1135.check_uvars; use_eq = false; is_iface = _52_1135.is_iface; admit = _52_1135.admit; lax = _52_1135.lax; type_of = _52_1135.type_of; universe_of = _52_1135.universe_of; use_bv_sorts = _52_1135.use_bv_sorts}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _143_1135 = (expected_typ env)
in ((

let _52_1142 = env
in {solver = _52_1142.solver; range = _52_1142.range; curmodule = _52_1142.curmodule; gamma = _52_1142.gamma; gamma_cache = _52_1142.gamma_cache; modules = _52_1142.modules; expected_typ = None; sigtab = _52_1142.sigtab; is_pattern = _52_1142.is_pattern; instantiate_imp = _52_1142.instantiate_imp; effects = _52_1142.effects; generalize = _52_1142.generalize; letrecs = _52_1142.letrecs; top_level = _52_1142.top_level; check_uvars = _52_1142.check_uvars; use_eq = false; is_iface = _52_1142.is_iface; admit = _52_1142.admit; lax = _52_1142.lax; type_of = _52_1142.type_of; universe_of = _52_1142.universe_of; use_bv_sorts = _52_1142.use_bv_sorts}), _143_1135)))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _143_1141 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1149, se) -> begin
(se)::[]
end
| _52_1154 -> begin
[]
end))))
in (FStar_All.pipe_right _143_1141 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1156 = (add_sigelts env sigs)
in (

let _52_1158 = env
in {solver = _52_1158.solver; range = _52_1158.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1158.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1158.expected_typ; sigtab = _52_1158.sigtab; is_pattern = _52_1158.is_pattern; instantiate_imp = _52_1158.instantiate_imp; effects = _52_1158.effects; generalize = _52_1158.generalize; letrecs = _52_1158.letrecs; top_level = _52_1158.top_level; check_uvars = _52_1158.check_uvars; use_eq = _52_1158.use_eq; is_iface = _52_1158.is_iface; admit = _52_1158.admit; lax = _52_1158.lax; type_of = _52_1158.type_of; universe_of = _52_1158.universe_of; use_bv_sorts = _52_1158.use_bv_sorts})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1171))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _143_1153 = (let _143_1152 = (FStar_Syntax_Free.uvars t)
in (ext out _143_1152))
in (aux _143_1153 tl))
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
(let _143_1165 = (let _143_1164 = (FStar_Syntax_Free.univs t)
in (ext out _143_1164))
in (aux _143_1165 tl))
end
| (Binding_sig (_52_1241))::_52_1239 -> begin
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


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _143_1172 = (let _143_1171 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _143_1171 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _143_1172 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1273) -> begin
(FStar_List.append lids keys)
end
| _52_1277 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1279 v keys -> (let _143_1195 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _143_1195 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1283 -> ()); push = (fun _52_1285 -> ()); pop = (fun _52_1287 -> ()); mark = (fun _52_1289 -> ()); reset_mark = (fun _52_1291 -> ()); commit_mark = (fun _52_1293 -> ()); encode_modul = (fun _52_1295 _52_1297 -> ()); encode_sig = (fun _52_1299 _52_1301 -> ()); solve = (fun _52_1303 _52_1305 _52_1307 -> ()); is_trivial = (fun _52_1309 _52_1311 -> false); finish = (fun _52_1313 -> ()); refresh = (fun _52_1314 -> ())}




