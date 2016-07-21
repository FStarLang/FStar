
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool} 
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


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _52_100 -> begin
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
| (FStar_Syntax_Syntax.Delta_abstract (l1), _52_149) -> begin
(aux l1 l2)
end
| (_52_152, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _144_387 = (aux l1 l2)
in Unfold (_144_387)))
end))


let default_table_size : Prims.int = 200


let new_sigtab = (fun _52_156 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let new_gamma_cache = (fun _52_157 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _144_419 = (new_gamma_cache ())
in (let _144_418 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _144_419; modules = []; expected_typ = None; sigtab = _144_418; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _52_173 = (let _144_473 = (let _144_472 = (FStar_ST.read stack)
in (env)::_144_472)
in (FStar_ST.op_Colon_Equals stack _144_473))
in (

let _52_175 = env
in (let _144_475 = (FStar_Util.smap_copy (gamma_cache env))
in (let _144_474 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_175.solver; range = _52_175.range; curmodule = _52_175.curmodule; gamma = _52_175.gamma; gamma_cache = _144_475; modules = _52_175.modules; expected_typ = _52_175.expected_typ; sigtab = _144_474; is_pattern = _52_175.is_pattern; instantiate_imp = _52_175.instantiate_imp; effects = _52_175.effects; generalize = _52_175.generalize; letrecs = _52_175.letrecs; top_level = _52_175.top_level; check_uvars = _52_175.check_uvars; use_eq = _52_175.use_eq; is_iface = _52_175.is_iface; admit = _52_175.admit; type_of = _52_175.type_of; universe_of = _52_175.universe_of; use_bv_sorts = _52_175.use_bv_sorts})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_182 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_185 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let mark = (fun env -> (push env))
in (

let commit_mark = (fun env -> (

let _52_190 = (let _144_482 = (pop env)
in (Prims.ignore _144_482))
in env))
in (

let reset_mark = (fun env -> (pop env))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop}))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_196 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_199 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_202 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_205 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_209 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_215 = e
in {solver = _52_215.solver; range = r; curmodule = _52_215.curmodule; gamma = _52_215.gamma; gamma_cache = _52_215.gamma_cache; modules = _52_215.modules; expected_typ = _52_215.expected_typ; sigtab = _52_215.sigtab; is_pattern = _52_215.is_pattern; instantiate_imp = _52_215.instantiate_imp; effects = _52_215.effects; generalize = _52_215.generalize; letrecs = _52_215.letrecs; top_level = _52_215.top_level; check_uvars = _52_215.check_uvars; use_eq = _52_215.use_eq; is_iface = _52_215.is_iface; admit = _52_215.admit; type_of = _52_215.type_of; universe_of = _52_215.universe_of; use_bv_sorts = _52_215.use_bv_sorts})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_222 = env
in {solver = _52_222.solver; range = _52_222.range; curmodule = lid; gamma = _52_222.gamma; gamma_cache = _52_222.gamma_cache; modules = _52_222.modules; expected_typ = _52_222.expected_typ; sigtab = _52_222.sigtab; is_pattern = _52_222.is_pattern; instantiate_imp = _52_222.instantiate_imp; effects = _52_222.effects; generalize = _52_222.generalize; letrecs = _52_222.letrecs; top_level = _52_222.top_level; check_uvars = _52_222.check_uvars; use_eq = _52_222.use_eq; is_iface = _52_222.is_iface; admit = _52_222.admit; type_of = _52_222.type_of; universe_of = _52_222.universe_of; use_bv_sorts = _52_222.use_bv_sorts}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _144_530 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _144_530)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun _52_231 -> (match (()) with
| () -> begin
(let _144_533 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_144_533))
end))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), _52_243) -> begin
(

let _52_245 = ()
in (

let n = ((FStar_List.length formals) - 1)
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _144_540 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_144_540))))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_258 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_266 -> (match (_52_266) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_269 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _144_556 = (let _144_555 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _144_554 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _144_553 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _144_552 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _144_555 _144_554 _144_553 _144_552)))))
in (FStar_All.failwith _144_556))
end else begin
()
end
in (let _144_557 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd _144_557))))
end
| _52_272 -> begin
(let _144_559 = (let _144_558 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _144_558))
in (FStar_All.failwith _144_559))
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
| ([], _52_283) -> begin
Maybe
end
| (_52_286, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_297 -> begin
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

let _52_303 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _144_579 = (let _144_578 = (inst_tscheme t)
in FStar_Util.Inl (_144_578))
in Some (_144_579))
end else begin
None
end
end
| Binding_sig (_52_312, FStar_Syntax_Syntax.Sig_bundle (ses, _52_315, _52_317, _52_319)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _144_581 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _144_581 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr (((se), (None)))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_332) -> begin
Some (t)
end
| _52_335 -> begin
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
| _52_342 -> begin
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
| Some (_52_352) -> begin
true
end))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_358, _52_360, _52_362) -> begin
(add_sigelts env ses)
end
| _52_366 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let _52_369 = (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_373) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| _52_379 -> begin
()
end)))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_3 -> (match (_52_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_388 -> begin
None
end))))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_4 -> (match (_52_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_395 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_399, (lb)::[]), _52_404, _52_406, _52_408) -> begin
(let _144_615 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_144_615))
end
| FStar_Syntax_Syntax.Sig_let ((_52_412, lbs), _52_416, _52_418, _52_420) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_425) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _144_617 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (_144_617))
end else begin
None
end
end)))
end
| _52_430 -> begin
None
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _144_625 = (let _144_624 = (let _144_623 = (variable_not_found bv)
in (let _144_622 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_144_623), (_144_622))))
in FStar_Syntax_Syntax.Error (_144_624))
in (Prims.raise _144_625))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_439) -> begin
(let _144_631 = (let _144_630 = (let _144_629 = (let _144_628 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _144_628))
in ((ne.FStar_Syntax_Syntax.univs), (_144_629)))
in (inst_tscheme _144_630))
in Some (_144_631))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_446, _52_448, _52_450) -> begin
(let _144_635 = (let _144_634 = (let _144_633 = (let _144_632 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _144_632))
in ((us), (_144_633)))
in (inst_tscheme _144_634))
in Some (_144_635))
end
| _52_454 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_464, t) -> begin
Some (t)
end)
end
| _52_469 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (

let mapper = (fun _52_5 -> (match (_52_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_476, uvs, t, _52_480, _52_482, _52_484, _52_486, _52_488), None) -> begin
(let _144_646 = (inst_tscheme ((uvs), (t)))
in Some (_144_646))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_499), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _144_647 = (inst_tscheme ((uvs), (t)))
in Some (_144_647))
end else begin
None
end
end else begin
(let _144_648 = (inst_tscheme ((uvs), (t)))
in Some (_144_648))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_510, _52_512, _52_514, _52_516), None) -> begin
(match (tps) with
| [] -> begin
(let _144_650 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _144_649 -> Some (_144_649)) _144_650))
end
| _52_524 -> begin
(let _144_655 = (let _144_654 = (let _144_653 = (let _144_652 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _144_652))
in ((uvs), (_144_653)))
in (inst_tscheme _144_654))
in (FStar_All.pipe_left (fun _144_651 -> Some (_144_651)) _144_655))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_530, _52_532, _52_534, _52_536), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _144_657 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _144_656 -> Some (_144_656)) _144_657))
end
| _52_545 -> begin
(let _144_662 = (let _144_661 = (let _144_660 = (let _144_659 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _144_659))
in ((uvs), (_144_660)))
in (inst_tscheme_with _144_661 us))
in (FStar_All.pipe_left (fun _144_658 -> Some (_144_658)) _144_662))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_549), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_554 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _144_663 = (lookup_qname env lid)
in (FStar_Util.bind_opt _144_663 mapper))) with
| Some (us, t) -> begin
Some (((us), ((

let _52_560 = t
in {FStar_Syntax_Syntax.n = _52_560.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_560.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_560.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_6 -> (match (_52_6) with
| FStar_Util.Inl (_52_567) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_571) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_575, _52_577, _52_579, qs, _52_582) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_586) -> begin
Some (true)
end
| _52_589 -> begin
Some (false)
end)
end))
in (match ((let _144_670 = (lookup_qname env lid)
in (FStar_Util.bind_opt _144_670 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _144_677 = (let _144_676 = (let _144_675 = (name_not_found l)
in ((_144_675), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_144_676))
in (Prims.raise _144_677))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_602, uvs, t, _52_606, _52_608), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_616 -> begin
(let _144_684 = (let _144_683 = (let _144_682 = (name_not_found lid)
in ((_144_682), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_144_683))
in (Prims.raise _144_684))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_620, uvs, t, _52_624, _52_626, _52_628, _52_630, _52_632), None)) -> begin
(inst_tscheme ((uvs), (t)))
end
| _52_640 -> begin
(let _144_691 = (let _144_690 = (let _144_689 = (name_not_found lid)
in ((_144_689), ((FStar_Ident.range_of_lid lid))))
in FStar_Syntax_Syntax.Error (_144_690))
in (Prims.raise _144_691))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_650, lbs), _52_654, _52_656, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _144_700 = (let _144_699 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in ((lb.FStar_Syntax_Syntax.lbunivs), (_144_699)))
in Some (_144_700))
end else begin
None
end)))
end
| _52_663 -> begin
None
end)
end
| _52_665 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _144_707 = (let _144_706 = (let _144_705 = (name_not_found ftv)
in ((_144_705), ((FStar_Ident.range_of_lid ftv))))
in FStar_Syntax_Syntax.Error (_144_706))
in (Prims.raise _144_707))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_675 -> (match (()) with
| () -> begin
(let _144_718 = (let _144_717 = (FStar_Util.string_of_int i)
in (let _144_716 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _144_717 _144_716)))
in (FStar_All.failwith _144_718))
end))
in (

let _52_679 = (lookup_datacon env lid)
in (match (_52_679) with
| (_52_677, t) -> begin
(match ((let _144_719 = (FStar_Syntax_Subst.compress t)
in _144_719.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_682) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _144_720 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _144_720 Prims.fst)))
end
end
| _52_687 -> begin
(fail ())
end)
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_691, uvs, t, q, _52_696), None)) -> begin
Some (((((uvs), (t))), (q)))
end
| _52_704 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_714), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_724 -> begin
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
| ([], _52_728) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_731, (_52_738)::(_52_735)::_52_733) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _144_734 = (let _144_733 = (FStar_Syntax_Print.lid_to_string lid)
in (let _144_732 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _144_733 _144_732)))
in (FStar_All.failwith _144_734))
end
| _52_742 -> begin
(

let _52_746 = (let _144_736 = (let _144_735 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_144_735)))
in (inst_tscheme_with _144_736 insts))
in (match (_52_746) with
| (_52_744, t) -> begin
(match ((let _144_737 = (FStar_Syntax_Subst.compress t)
in _144_737.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| _52_752 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_754 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create 20)
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_762, c) -> begin
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

let _52_776 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_782, _52_784, _52_786, _52_788, _52_790, dcs, _52_793, _52_795), _52_799)) -> begin
dcs
end
| _52_804 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_808, _52_810, _52_812, l, _52_815, _52_817, _52_819, _52_821), _52_825)) -> begin
l
end
| _52_830 -> begin
(let _144_753 = (let _144_752 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _144_752))
in (FStar_All.failwith _144_753))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_834, _52_836, _52_838, _52_840, _52_842, _52_844, _52_846, _52_848), _52_852)) -> begin
true
end
| _52_857 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_861, _52_863, _52_865, _52_867, _52_869, _52_871, tags, _52_874), _52_878)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_890 -> begin
false
end)) tags)
end
| _52_892 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_896, _52_898, _52_900, quals, _52_903), _52_907)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_913) -> begin
true
end
| _52_916 -> begin
false
end)) quals)
end
| _52_918 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _144_772 = (FStar_Syntax_Util.un_uinst head)
in _144_772.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_924 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _144_784 = (let _144_783 = (let _144_782 = (name_not_found l)
in ((_144_782), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_144_783))
in (Prims.raise _144_784))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_952 -> (match (_52_952) with
| (m1, m2, _52_947, _52_949, _52_951) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _144_860 = (let _144_859 = (let _144_858 = (let _144_857 = (FStar_Syntax_Print.lid_to_string l1)
in (let _144_856 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _144_857 _144_856)))
in ((_144_858), (env.range)))
in FStar_Syntax_Syntax.Error (_144_859))
in (Prims.raise _144_860))
end
| Some (_52_955, _52_957, m3, j1, j2) -> begin
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
(let _144_875 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _144_875))
end
| Some (md) -> begin
(

let _52_978 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (_52_978) with
| (_52_976, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_987))::((wp, _52_983))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _52_995 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_1002) -> begin
(

let effects = (

let _52_1005 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1005.order; joins = _52_1005.joins})
in (

let _52_1008 = env
in {solver = _52_1008.solver; range = _52_1008.range; curmodule = _52_1008.curmodule; gamma = _52_1008.gamma; gamma_cache = _52_1008.gamma_cache; modules = _52_1008.modules; expected_typ = _52_1008.expected_typ; sigtab = _52_1008.sigtab; is_pattern = _52_1008.is_pattern; instantiate_imp = _52_1008.instantiate_imp; effects = effects; generalize = _52_1008.generalize; letrecs = _52_1008.letrecs; top_level = _52_1008.top_level; check_uvars = _52_1008.check_uvars; use_eq = _52_1008.use_eq; is_iface = _52_1008.is_iface; admit = _52_1008.admit; type_of = _52_1008.type_of; universe_of = _52_1008.universe_of; use_bv_sorts = _52_1008.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1012) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _144_890 = (e1.mlift r wp1)
in (e2.mlift r _144_890)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1027 = (inst_tscheme lift_t)
in (match (_52_1027) with
| (_52_1025, lift_t) -> begin
(let _144_902 = (let _144_901 = (let _144_900 = (let _144_899 = (FStar_Syntax_Syntax.as_arg r)
in (let _144_898 = (let _144_897 = (FStar_Syntax_Syntax.as_arg wp1)
in (_144_897)::[])
in (_144_899)::_144_898))
in ((lift_t), (_144_900)))
in FStar_Syntax_Syntax.Tm_app (_144_901))
in (FStar_Syntax_Syntax.mk _144_902 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift_wp)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _144_919 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _144_919 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _144_920 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _144_920 FStar_Syntax_Syntax.Delta_constant None))
in (let _144_921 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _144_921)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1044 -> (match (_52_1044) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _144_927 -> Some (_144_927)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _144_935 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _144_934 = (find_edge order ((i), (k)))
in (let _144_933 = (find_edge order ((k), (j)))
in ((_144_934), (_144_933))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1056 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _144_935))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _144_1027 = (find_edge order ((i), (k)))
in (let _144_1026 = (find_edge order ((j), (k)))
in ((_144_1027), (_144_1026))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _52_1073, _52_1075) -> begin
if ((let _144_1028 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _144_1028)) && (not ((let _144_1029 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _144_1029))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _52_1079 -> begin
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

let _52_1088 = env.effects
in {decls = _52_1088.decls; order = order; joins = joins})
in (

let _52_1091 = env
in {solver = _52_1091.solver; range = _52_1091.range; curmodule = _52_1091.curmodule; gamma = _52_1091.gamma; gamma_cache = _52_1091.gamma_cache; modules = _52_1091.modules; expected_typ = _52_1091.expected_typ; sigtab = _52_1091.sigtab; is_pattern = _52_1091.is_pattern; instantiate_imp = _52_1091.instantiate_imp; effects = effects; generalize = _52_1091.generalize; letrecs = _52_1091.letrecs; top_level = _52_1091.top_level; check_uvars = _52_1091.check_uvars; use_eq = _52_1091.use_eq; is_iface = _52_1091.is_iface; admit = _52_1091.admit; type_of = _52_1091.type_of; universe_of = _52_1091.universe_of; use_bv_sorts = _52_1091.use_bv_sorts})))))))))))))
end
| _52_1094 -> begin
env
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _144_1078 = (

let _52_1097 = env
in (let _144_1077 = (let _144_1076 = (let _144_1075 = (let _144_1074 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_144_1074), (s)))
in Binding_sig (_144_1075))
in (_144_1076)::env.gamma)
in {solver = _52_1097.solver; range = _52_1097.range; curmodule = _52_1097.curmodule; gamma = _144_1077; gamma_cache = _52_1097.gamma_cache; modules = _52_1097.modules; expected_typ = _52_1097.expected_typ; sigtab = _52_1097.sigtab; is_pattern = _52_1097.is_pattern; instantiate_imp = _52_1097.instantiate_imp; effects = _52_1097.effects; generalize = _52_1097.generalize; letrecs = _52_1097.letrecs; top_level = _52_1097.top_level; check_uvars = _52_1097.check_uvars; use_eq = _52_1097.use_eq; is_iface = _52_1097.is_iface; admit = _52_1097.admit; type_of = _52_1097.type_of; universe_of = _52_1097.universe_of; use_bv_sorts = _52_1097.use_bv_sorts}))
in (build_lattice _144_1078 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _144_1089 = (

let _52_1102 = env
in (let _144_1088 = (let _144_1087 = (let _144_1086 = (let _144_1085 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_144_1085), (s), (us)))
in Binding_sig_inst (_144_1086))
in (_144_1087)::env.gamma)
in {solver = _52_1102.solver; range = _52_1102.range; curmodule = _52_1102.curmodule; gamma = _144_1088; gamma_cache = _52_1102.gamma_cache; modules = _52_1102.modules; expected_typ = _52_1102.expected_typ; sigtab = _52_1102.sigtab; is_pattern = _52_1102.is_pattern; instantiate_imp = _52_1102.instantiate_imp; effects = _52_1102.effects; generalize = _52_1102.generalize; letrecs = _52_1102.letrecs; top_level = _52_1102.top_level; check_uvars = _52_1102.check_uvars; use_eq = _52_1102.use_eq; is_iface = _52_1102.is_iface; admit = _52_1102.admit; type_of = _52_1102.type_of; universe_of = _52_1102.universe_of; use_bv_sorts = _52_1102.use_bv_sorts}))
in (build_lattice _144_1089 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1106 = env
in {solver = _52_1106.solver; range = _52_1106.range; curmodule = _52_1106.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1106.gamma_cache; modules = _52_1106.modules; expected_typ = _52_1106.expected_typ; sigtab = _52_1106.sigtab; is_pattern = _52_1106.is_pattern; instantiate_imp = _52_1106.instantiate_imp; effects = _52_1106.effects; generalize = _52_1106.generalize; letrecs = _52_1106.letrecs; top_level = _52_1106.top_level; check_uvars = _52_1106.check_uvars; use_eq = _52_1106.use_eq; is_iface = _52_1106.is_iface; admit = _52_1106.admit; type_of = _52_1106.type_of; universe_of = _52_1106.universe_of; use_bv_sorts = _52_1106.use_bv_sorts}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1116 -> (match (_52_1116) with
| (x, _52_1115) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1121 = ()
in (

let x = (

let _52_1123 = x
in {FStar_Syntax_Syntax.ppname = _52_1123.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1123.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1133 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1135 = env
in {solver = _52_1135.solver; range = _52_1135.range; curmodule = _52_1135.curmodule; gamma = []; gamma_cache = _52_1135.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1135.sigtab; is_pattern = _52_1135.is_pattern; instantiate_imp = _52_1135.instantiate_imp; effects = _52_1135.effects; generalize = _52_1135.generalize; letrecs = _52_1135.letrecs; top_level = _52_1135.top_level; check_uvars = _52_1135.check_uvars; use_eq = _52_1135.use_eq; is_iface = _52_1135.is_iface; admit = _52_1135.admit; type_of = _52_1135.type_of; universe_of = _52_1135.universe_of; use_bv_sorts = _52_1135.use_bv_sorts})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1143 = env
in {solver = _52_1143.solver; range = _52_1143.range; curmodule = _52_1143.curmodule; gamma = _52_1143.gamma; gamma_cache = _52_1143.gamma_cache; modules = _52_1143.modules; expected_typ = Some (t); sigtab = _52_1143.sigtab; is_pattern = _52_1143.is_pattern; instantiate_imp = _52_1143.instantiate_imp; effects = _52_1143.effects; generalize = _52_1143.generalize; letrecs = _52_1143.letrecs; top_level = _52_1143.top_level; check_uvars = _52_1143.check_uvars; use_eq = false; is_iface = _52_1143.is_iface; admit = _52_1143.admit; type_of = _52_1143.type_of; universe_of = _52_1143.universe_of; use_bv_sorts = _52_1143.use_bv_sorts}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _144_1132 = (expected_typ env)
in (((

let _52_1150 = env
in {solver = _52_1150.solver; range = _52_1150.range; curmodule = _52_1150.curmodule; gamma = _52_1150.gamma; gamma_cache = _52_1150.gamma_cache; modules = _52_1150.modules; expected_typ = None; sigtab = _52_1150.sigtab; is_pattern = _52_1150.is_pattern; instantiate_imp = _52_1150.instantiate_imp; effects = _52_1150.effects; generalize = _52_1150.generalize; letrecs = _52_1150.letrecs; top_level = _52_1150.top_level; check_uvars = _52_1150.check_uvars; use_eq = false; is_iface = _52_1150.is_iface; admit = _52_1150.admit; type_of = _52_1150.type_of; universe_of = _52_1150.universe_of; use_bv_sorts = _52_1150.use_bv_sorts})), (_144_1132))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _144_1138 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1157, se) -> begin
(se)::[]
end
| _52_1162 -> begin
[]
end))))
in (FStar_All.pipe_right _144_1138 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1164 = (add_sigelts env sigs)
in (

let _52_1166 = env
in {solver = _52_1166.solver; range = _52_1166.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1166.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1166.expected_typ; sigtab = _52_1166.sigtab; is_pattern = _52_1166.is_pattern; instantiate_imp = _52_1166.instantiate_imp; effects = _52_1166.effects; generalize = _52_1166.generalize; letrecs = _52_1166.letrecs; top_level = _52_1166.top_level; check_uvars = _52_1166.check_uvars; use_eq = _52_1166.use_eq; is_iface = _52_1166.is_iface; admit = _52_1166.admit; type_of = _52_1166.type_of; universe_of = _52_1166.universe_of; use_bv_sorts = _52_1166.use_bv_sorts})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1179))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _144_1150 = (let _144_1149 = (FStar_Syntax_Free.uvars t)
in (ext out _144_1149))
in (aux _144_1150 tl))
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
(let _144_1162 = (let _144_1161 = (FStar_Syntax_Free.univs t)
in (ext out _144_1161))
in (aux _144_1162 tl))
end
| (Binding_sig (_52_1248))::tl -> begin
(aux out tl)
end))
in (aux no_univs env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _52_11 -> (match (_52_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _144_1169 = (let _144_1168 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _144_1168 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _144_1169 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1280) -> begin
(FStar_List.append lids keys)
end
| _52_1284 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1286 v keys -> (let _144_1192 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _144_1192 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1290 -> ()); push = (fun _52_1292 -> ()); pop = (fun _52_1294 -> ()); mark = (fun _52_1296 -> ()); reset_mark = (fun _52_1298 -> ()); commit_mark = (fun _52_1300 -> ()); encode_modul = (fun _52_1302 _52_1304 -> ()); encode_sig = (fun _52_1306 _52_1308 -> ()); solve = (fun _52_1310 _52_1312 _52_1314 -> ()); is_trivial = (fun _52_1316 _52_1318 -> false); finish = (fun _52_1320 -> ()); refresh = (fun _52_1321 -> ())}


let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _144_1230 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc (fun _52_1323 _52_1325 -> FStar_Syntax_Syntax.U_zero) dummy_solver _144_1230)))




