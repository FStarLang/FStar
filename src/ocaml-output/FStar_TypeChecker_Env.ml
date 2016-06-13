
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


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _52_100 -> begin
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
| (FStar_Syntax_Syntax.Delta_abstract (l1), _52_149) -> begin
(aux l1 l2)
end
| (_52_152, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _142_387 = (aux l1 l2)
in Unfold (_142_387)))
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


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _142_409 = (new_gamma_cache ())
in (let _142_408 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _142_409; modules = []; expected_typ = None; sigtab = _142_408; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _52_174 = (let _142_463 = (let _142_462 = (FStar_ST.read stack)
in (env)::_142_462)
in (FStar_ST.op_Colon_Equals stack _142_463))
in (

let _52_176 = env
in (let _142_465 = (FStar_Util.smap_copy (gamma_cache env))
in (let _142_464 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_176.solver; range = _52_176.range; curmodule = _52_176.curmodule; gamma = _52_176.gamma; gamma_cache = _142_465; modules = _52_176.modules; expected_typ = _52_176.expected_typ; sigtab = _142_464; is_pattern = _52_176.is_pattern; instantiate_imp = _52_176.instantiate_imp; effects = _52_176.effects; generalize = _52_176.generalize; letrecs = _52_176.letrecs; top_level = _52_176.top_level; check_uvars = _52_176.check_uvars; use_eq = _52_176.use_eq; is_iface = _52_176.is_iface; admit = _52_176.admit; type_of = _52_176.type_of; universe_of = _52_176.universe_of; use_bv_sorts = _52_176.use_bv_sorts})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _52_183 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_186 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let mark = (fun env -> (push env))
in (

let commit_mark = (fun env -> (

let _52_191 = (let _142_472 = (pop env)
in (Prims.ignore _142_472))
in env))
in (

let reset_mark = (fun env -> (pop env))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop}))))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_197 = (env.solver.push msg)
in (stack_ops.es_push env)))


let mark : env  ->  env = (fun env -> (

let _52_200 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))


let commit_mark : env  ->  env = (fun env -> (

let _52_203 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))


let reset_mark : env  ->  env = (fun env -> (

let _52_206 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (

let _52_210 = (env.solver.pop msg)
in (stack_ops.es_pop env)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _52_216 = e
in {solver = _52_216.solver; range = r; curmodule = _52_216.curmodule; gamma = _52_216.gamma; gamma_cache = _52_216.gamma_cache; modules = _52_216.modules; expected_typ = _52_216.expected_typ; sigtab = _52_216.sigtab; is_pattern = _52_216.is_pattern; instantiate_imp = _52_216.instantiate_imp; effects = _52_216.effects; generalize = _52_216.generalize; letrecs = _52_216.letrecs; top_level = _52_216.top_level; check_uvars = _52_216.check_uvars; use_eq = _52_216.use_eq; is_iface = _52_216.is_iface; admit = _52_216.admit; type_of = _52_216.type_of; universe_of = _52_216.universe_of; use_bv_sorts = _52_216.use_bv_sorts})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_223 = env
in {solver = _52_223.solver; range = _52_223.range; curmodule = lid; gamma = _52_223.gamma; gamma_cache = _52_223.gamma_cache; modules = _52_223.modules; expected_typ = _52_223.expected_typ; sigtab = _52_223.sigtab; is_pattern = _52_223.is_pattern; instantiate_imp = _52_223.instantiate_imp; effects = _52_223.effects; generalize = _52_223.generalize; letrecs = _52_223.letrecs; top_level = _52_223.top_level; check_uvars = _52_223.check_uvars; use_eq = _52_223.use_eq; is_iface = _52_223.is_iface; admit = _52_223.admit; type_of = _52_223.type_of; universe_of = _52_223.universe_of; use_bv_sorts = _52_223.use_bv_sorts}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _142_520 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _142_520)))


let new_u_univ = (fun _52_232 -> (let _142_522 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_142_522)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _52_245) -> begin
(

let _52_247 = ()
in (

let n = ((FStar_List.length formals) - 1)
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _142_529 = (FStar_Syntax_Subst.subst vs t)
in (us, _142_529)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_260 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_268 -> (match (_52_268) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _52_271 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _142_545 = (let _142_544 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _142_543 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _142_542 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _142_541 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _142_544 _142_543 _142_542 _142_541)))))
in (FStar_All.failwith _142_545))
end else begin
()
end
in (let _142_546 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _142_546))))
end
| _52_274 -> begin
(let _142_548 = (let _142_547 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _142_547))
in (FStar_All.failwith _142_548))
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
| ([], _52_285) -> begin
Maybe
end
| (_52_288, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_299 -> begin
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

let _52_305 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _142_568 = (let _142_567 = (inst_tscheme t)
in FStar_Util.Inl (_142_567))
in Some (_142_568))
end else begin
None
end
end
| Binding_sig (_52_314, FStar_Syntax_Syntax.Sig_bundle (ses, _52_317, _52_319, _52_321)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _142_570 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _142_570 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_334) -> begin
Some (t)
end
| _52_337 -> begin
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
| _52_344 -> begin
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
| Some (_52_354) -> begin
true
end))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_360, _52_362, _52_364) -> begin
(add_sigelts env ses)
end
| _52_368 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_3 -> (match (_52_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_379 -> begin
None
end))))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_4 -> (match (_52_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_386 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_390, (lb)::[]), _52_395, _52_397, _52_399) -> begin
(let _142_603 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_142_603))
end
| FStar_Syntax_Syntax.Sig_let ((_52_403, lbs), _52_407, _52_409, _52_411) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_416) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _142_605 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_142_605))
end else begin
None
end
end)))
end
| _52_421 -> begin
None
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _142_613 = (let _142_612 = (let _142_611 = (variable_not_found bv)
in (let _142_610 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_142_611, _142_610)))
in FStar_Syntax_Syntax.Error (_142_612))
in (Prims.raise _142_613))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_430) -> begin
(let _142_619 = (let _142_618 = (let _142_617 = (let _142_616 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _142_616))
in (ne.FStar_Syntax_Syntax.univs, _142_617))
in (inst_tscheme _142_618))
in Some (_142_619))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_437, _52_439, _52_441) -> begin
(let _142_623 = (let _142_622 = (let _142_621 = (let _142_620 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _142_620))
in (us, _142_621))
in (inst_tscheme _142_622))
in Some (_142_623))
end
| _52_445 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_455, t) -> begin
Some (t)
end)
end
| _52_460 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (

let mapper = (fun _52_5 -> (match (_52_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_467, uvs, t, _52_471, _52_473, _52_475, _52_477, _52_479), None) -> begin
(let _142_634 = (inst_tscheme (uvs, t))
in Some (_142_634))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_490), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _142_635 = (inst_tscheme (uvs, t))
in Some (_142_635))
end else begin
None
end
end else begin
(let _142_636 = (inst_tscheme (uvs, t))
in Some (_142_636))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_501, _52_503, _52_505, _52_507), None) -> begin
(match (tps) with
| [] -> begin
(let _142_638 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _142_637 -> Some (_142_637)) _142_638))
end
| _52_515 -> begin
(let _142_643 = (let _142_642 = (let _142_641 = (let _142_640 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _142_640))
in (uvs, _142_641))
in (inst_tscheme _142_642))
in (FStar_All.pipe_left (fun _142_639 -> Some (_142_639)) _142_643))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_521, _52_523, _52_525, _52_527), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _142_645 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _142_644 -> Some (_142_644)) _142_645))
end
| _52_536 -> begin
(let _142_650 = (let _142_649 = (let _142_648 = (let _142_647 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _142_647))
in (uvs, _142_648))
in (inst_tscheme_with _142_649 us))
in (FStar_All.pipe_left (fun _142_646 -> Some (_142_646)) _142_650))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_540), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_545 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _142_651 = (lookup_qname env lid)
in (FStar_Util.bind_opt _142_651 mapper))) with
| Some (us, t) -> begin
Some ((us, (

let _52_551 = t
in {FStar_Syntax_Syntax.n = _52_551.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_551.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_551.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _52_6 -> (match (_52_6) with
| FStar_Util.Inl (_52_558) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_562) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_566, _52_568, _52_570, qs, _52_573) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_577) -> begin
Some (true)
end
| _52_580 -> begin
Some (false)
end)
end))
in (match ((let _142_658 = (lookup_qname env lid)
in (FStar_Util.bind_opt _142_658 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _142_665 = (let _142_664 = (let _142_663 = (name_not_found l)
in (_142_663, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_142_664))
in (Prims.raise _142_665))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_593, uvs, t, _52_597, _52_599), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_607 -> begin
(let _142_672 = (let _142_671 = (let _142_670 = (name_not_found lid)
in (_142_670, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_142_671))
in (Prims.raise _142_672))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_611, uvs, t, _52_615, _52_617, _52_619, _52_621, _52_623), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_631 -> begin
(let _142_679 = (let _142_678 = (let _142_677 = (name_not_found lid)
in (_142_677, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_142_678))
in (Prims.raise _142_679))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_641, lbs), _52_645, _52_647, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _142_688 = (let _142_687 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _142_687))
in Some (_142_688))
end else begin
None
end)))
end
| _52_654 -> begin
None
end)
end
| _52_656 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _142_695 = (let _142_694 = (let _142_693 = (name_not_found ftv)
in (_142_693, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_142_694))
in (Prims.raise _142_695))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_666 -> (match (()) with
| () -> begin
(let _142_706 = (let _142_705 = (FStar_Util.string_of_int i)
in (let _142_704 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _142_705 _142_704)))
in (FStar_All.failwith _142_706))
end))
in (

let _52_670 = (lookup_datacon env lid)
in (match (_52_670) with
| (_52_668, t) -> begin
(match ((let _142_707 = (FStar_Syntax_Subst.compress t)
in _142_707.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_673) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _142_708 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _142_708 Prims.fst)))
end
end
| _52_678 -> begin
(fail ())
end)
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_682, uvs, t, q, _52_687), None)) -> begin
Some (((uvs, t), q))
end
| _52_695 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_705), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_715 -> begin
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
| ([], _52_719) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_722, (_52_729)::(_52_726)::_52_724) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _142_722 = (let _142_721 = (FStar_Syntax_Print.lid_to_string lid)
in (let _142_720 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _142_721 _142_720)))
in (FStar_All.failwith _142_722))
end
| _52_733 -> begin
(

let _52_737 = (let _142_724 = (let _142_723 = (FStar_Syntax_Util.arrow binders c)
in (univs, _142_723))
in (inst_tscheme_with _142_724 insts))
in (match (_52_737) with
| (_52_735, t) -> begin
(match ((let _142_725 = (FStar_Syntax_Subst.compress t)
in _142_725.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _52_743 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_745 -> begin
None
end))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create 20)
in (fun env l -> (

let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_753, c) -> begin
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

let _52_767 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_773, _52_775, _52_777, _52_779, _52_781, dcs, _52_784, _52_786), _52_790)) -> begin
dcs
end
| _52_795 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_799, _52_801, _52_803, l, _52_806, _52_808, _52_810, _52_812), _52_816)) -> begin
l
end
| _52_821 -> begin
(let _142_741 = (let _142_740 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _142_740))
in (FStar_All.failwith _142_741))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_825, _52_827, _52_829, _52_831, _52_833, _52_835, _52_837, _52_839), _52_843)) -> begin
true
end
| _52_848 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_852, _52_854, _52_856, _52_858, _52_860, _52_862, tags, _52_865), _52_869)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_881 -> begin
false
end)) tags)
end
| _52_883 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_887, _52_889, _52_891, quals, _52_894), _52_898)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_904) -> begin
true
end
| _52_907 -> begin
false
end)) quals)
end
| _52_909 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _142_760 = (FStar_Syntax_Util.un_uinst head)
in _142_760.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_915 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _142_772 = (let _142_771 = (let _142_770 = (name_not_found l)
in (_142_770, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_142_771))
in (Prims.raise _142_772))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_943 -> (match (_52_943) with
| (m1, m2, _52_938, _52_940, _52_942) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _142_848 = (let _142_847 = (let _142_846 = (let _142_845 = (FStar_Syntax_Print.lid_to_string l1)
in (let _142_844 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _142_845 _142_844)))
in (_142_846, env.range))
in FStar_Syntax_Syntax.Error (_142_847))
in (Prims.raise _142_848))
end
| Some (_52_946, _52_948, m3, j1, j2) -> begin
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
(let _142_863 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _142_863))
end
| Some (md) -> begin
(

let _52_969 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_52_969) with
| (_52_967, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, _52_978))::((wp, _52_974))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _52_986 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_993) -> begin
(

let effects = (

let _52_996 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_996.order; joins = _52_996.joins})
in (

let _52_999 = env
in {solver = _52_999.solver; range = _52_999.range; curmodule = _52_999.curmodule; gamma = _52_999.gamma; gamma_cache = _52_999.gamma_cache; modules = _52_999.modules; expected_typ = _52_999.expected_typ; sigtab = _52_999.sigtab; is_pattern = _52_999.is_pattern; instantiate_imp = _52_999.instantiate_imp; effects = effects; generalize = _52_999.generalize; letrecs = _52_999.letrecs; top_level = _52_999.top_level; check_uvars = _52_999.check_uvars; use_eq = _52_999.use_eq; is_iface = _52_999.is_iface; admit = _52_999.admit; type_of = _52_999.type_of; universe_of = _52_999.universe_of; use_bv_sorts = _52_999.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1003) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _142_878 = (e1.mlift r wp1)
in (e2.mlift r _142_878)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1018 = (inst_tscheme lift_t)
in (match (_52_1018) with
| (_52_1016, lift_t) -> begin
(let _142_890 = (let _142_889 = (let _142_888 = (let _142_887 = (FStar_Syntax_Syntax.as_arg r)
in (let _142_886 = (let _142_885 = (FStar_Syntax_Syntax.as_arg wp1)
in (_142_885)::[])
in (_142_887)::_142_886))
in (lift_t, _142_888))
in FStar_Syntax_Syntax.Tm_app (_142_889))
in (FStar_Syntax_Syntax.mk _142_890 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _142_907 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _142_907 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _142_908 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _142_908 FStar_Syntax_Syntax.Delta_constant None))
in (let _142_909 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _142_909)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1035 -> (match (_52_1035) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _142_915 -> Some (_142_915)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _142_923 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _142_922 = (find_edge order (i, k))
in (let _142_921 = (find_edge order (k, j))
in (_142_922, _142_921)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1047 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _142_923))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _142_1015 = (find_edge order (i, k))
in (let _142_1014 = (find_edge order (j, k))
in (_142_1015, _142_1014)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _52_1064, _52_1066) -> begin
if ((let _142_1016 = (find_edge order (k, ub))
in (FStar_Util.is_some _142_1016)) && (not ((let _142_1017 = (find_edge order (ub, k))
in (FStar_Util.is_some _142_1017))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _52_1070 -> begin
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

let _52_1079 = env.effects
in {decls = _52_1079.decls; order = order; joins = joins})
in (

let _52_1082 = env
in {solver = _52_1082.solver; range = _52_1082.range; curmodule = _52_1082.curmodule; gamma = _52_1082.gamma; gamma_cache = _52_1082.gamma_cache; modules = _52_1082.modules; expected_typ = _52_1082.expected_typ; sigtab = _52_1082.sigtab; is_pattern = _52_1082.is_pattern; instantiate_imp = _52_1082.instantiate_imp; effects = effects; generalize = _52_1082.generalize; letrecs = _52_1082.letrecs; top_level = _52_1082.top_level; check_uvars = _52_1082.check_uvars; use_eq = _52_1082.use_eq; is_iface = _52_1082.is_iface; admit = _52_1082.admit; type_of = _52_1082.type_of; universe_of = _52_1082.universe_of; use_bv_sorts = _52_1082.use_bv_sorts})))))))))))))
end
| _52_1085 -> begin
env
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _142_1066 = (

let _52_1088 = env
in (let _142_1065 = (let _142_1064 = (let _142_1063 = (let _142_1062 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_142_1062, s))
in Binding_sig (_142_1063))
in (_142_1064)::env.gamma)
in {solver = _52_1088.solver; range = _52_1088.range; curmodule = _52_1088.curmodule; gamma = _142_1065; gamma_cache = _52_1088.gamma_cache; modules = _52_1088.modules; expected_typ = _52_1088.expected_typ; sigtab = _52_1088.sigtab; is_pattern = _52_1088.is_pattern; instantiate_imp = _52_1088.instantiate_imp; effects = _52_1088.effects; generalize = _52_1088.generalize; letrecs = _52_1088.letrecs; top_level = _52_1088.top_level; check_uvars = _52_1088.check_uvars; use_eq = _52_1088.use_eq; is_iface = _52_1088.is_iface; admit = _52_1088.admit; type_of = _52_1088.type_of; universe_of = _52_1088.universe_of; use_bv_sorts = _52_1088.use_bv_sorts}))
in (build_lattice _142_1066 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _142_1077 = (

let _52_1093 = env
in (let _142_1076 = (let _142_1075 = (let _142_1074 = (let _142_1073 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_142_1073, s, us))
in Binding_sig_inst (_142_1074))
in (_142_1075)::env.gamma)
in {solver = _52_1093.solver; range = _52_1093.range; curmodule = _52_1093.curmodule; gamma = _142_1076; gamma_cache = _52_1093.gamma_cache; modules = _52_1093.modules; expected_typ = _52_1093.expected_typ; sigtab = _52_1093.sigtab; is_pattern = _52_1093.is_pattern; instantiate_imp = _52_1093.instantiate_imp; effects = _52_1093.effects; generalize = _52_1093.generalize; letrecs = _52_1093.letrecs; top_level = _52_1093.top_level; check_uvars = _52_1093.check_uvars; use_eq = _52_1093.use_eq; is_iface = _52_1093.is_iface; admit = _52_1093.admit; type_of = _52_1093.type_of; universe_of = _52_1093.universe_of; use_bv_sorts = _52_1093.use_bv_sorts}))
in (build_lattice _142_1077 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1097 = env
in {solver = _52_1097.solver; range = _52_1097.range; curmodule = _52_1097.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1097.gamma_cache; modules = _52_1097.modules; expected_typ = _52_1097.expected_typ; sigtab = _52_1097.sigtab; is_pattern = _52_1097.is_pattern; instantiate_imp = _52_1097.instantiate_imp; effects = _52_1097.effects; generalize = _52_1097.generalize; letrecs = _52_1097.letrecs; top_level = _52_1097.top_level; check_uvars = _52_1097.check_uvars; use_eq = _52_1097.use_eq; is_iface = _52_1097.is_iface; admit = _52_1097.admit; type_of = _52_1097.type_of; universe_of = _52_1097.universe_of; use_bv_sorts = _52_1097.use_bv_sorts}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1107 -> (match (_52_1107) with
| (x, _52_1106) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1112 = ()
in (

let x = (

let _52_1114 = x
in {FStar_Syntax_Syntax.ppname = _52_1114.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1114.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1124 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1126 = env
in {solver = _52_1126.solver; range = _52_1126.range; curmodule = _52_1126.curmodule; gamma = []; gamma_cache = _52_1126.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1126.sigtab; is_pattern = _52_1126.is_pattern; instantiate_imp = _52_1126.instantiate_imp; effects = _52_1126.effects; generalize = _52_1126.generalize; letrecs = _52_1126.letrecs; top_level = _52_1126.top_level; check_uvars = _52_1126.check_uvars; use_eq = _52_1126.use_eq; is_iface = _52_1126.is_iface; admit = _52_1126.admit; type_of = _52_1126.type_of; universe_of = _52_1126.universe_of; use_bv_sorts = _52_1126.use_bv_sorts})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1134 = env
in {solver = _52_1134.solver; range = _52_1134.range; curmodule = _52_1134.curmodule; gamma = _52_1134.gamma; gamma_cache = _52_1134.gamma_cache; modules = _52_1134.modules; expected_typ = Some (t); sigtab = _52_1134.sigtab; is_pattern = _52_1134.is_pattern; instantiate_imp = _52_1134.instantiate_imp; effects = _52_1134.effects; generalize = _52_1134.generalize; letrecs = _52_1134.letrecs; top_level = _52_1134.top_level; check_uvars = _52_1134.check_uvars; use_eq = false; is_iface = _52_1134.is_iface; admit = _52_1134.admit; type_of = _52_1134.type_of; universe_of = _52_1134.universe_of; use_bv_sorts = _52_1134.use_bv_sorts}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _142_1120 = (expected_typ env)
in ((

let _52_1141 = env
in {solver = _52_1141.solver; range = _52_1141.range; curmodule = _52_1141.curmodule; gamma = _52_1141.gamma; gamma_cache = _52_1141.gamma_cache; modules = _52_1141.modules; expected_typ = None; sigtab = _52_1141.sigtab; is_pattern = _52_1141.is_pattern; instantiate_imp = _52_1141.instantiate_imp; effects = _52_1141.effects; generalize = _52_1141.generalize; letrecs = _52_1141.letrecs; top_level = _52_1141.top_level; check_uvars = _52_1141.check_uvars; use_eq = false; is_iface = _52_1141.is_iface; admit = _52_1141.admit; type_of = _52_1141.type_of; universe_of = _52_1141.universe_of; use_bv_sorts = _52_1141.use_bv_sorts}), _142_1120)))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _142_1126 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1148, se) -> begin
(se)::[]
end
| _52_1153 -> begin
[]
end))))
in (FStar_All.pipe_right _142_1126 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1155 = (add_sigelts env sigs)
in (

let _52_1157 = env
in {solver = _52_1157.solver; range = _52_1157.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1157.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1157.expected_typ; sigtab = _52_1157.sigtab; is_pattern = _52_1157.is_pattern; instantiate_imp = _52_1157.instantiate_imp; effects = _52_1157.effects; generalize = _52_1157.generalize; letrecs = _52_1157.letrecs; top_level = _52_1157.top_level; check_uvars = _52_1157.check_uvars; use_eq = _52_1157.use_eq; is_iface = _52_1157.is_iface; admit = _52_1157.admit; type_of = _52_1157.type_of; universe_of = _52_1157.universe_of; use_bv_sorts = _52_1157.use_bv_sorts})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (_52_1170))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _142_1138 = (let _142_1137 = (FStar_Syntax_Free.uvars t)
in (ext out _142_1137))
in (aux _142_1138 tl))
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
(let _142_1150 = (let _142_1149 = (FStar_Syntax_Free.univs t)
in (ext out _142_1149))
in (aux _142_1150 tl))
end
| (Binding_sig (_52_1240))::_52_1238 -> begin
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


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _142_1157 = (let _142_1156 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _142_1156 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _142_1157 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1272) -> begin
(FStar_List.append lids keys)
end
| _52_1276 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1278 v keys -> (let _142_1180 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _142_1180 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1282 -> ()); push = (fun _52_1284 -> ()); pop = (fun _52_1286 -> ()); mark = (fun _52_1288 -> ()); reset_mark = (fun _52_1290 -> ()); commit_mark = (fun _52_1292 -> ()); encode_modul = (fun _52_1294 _52_1296 -> ()); encode_sig = (fun _52_1298 _52_1300 -> ()); solve = (fun _52_1302 _52_1304 _52_1306 -> ()); is_trivial = (fun _52_1308 _52_1310 -> false); finish = (fun _52_1312 -> ()); refresh = (fun _52_1313 -> ())}


let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _142_1216 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _142_1216)))




