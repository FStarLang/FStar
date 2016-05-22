
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
in (let _141_387 = (aux l1 l2)
in Unfold (_141_387)))
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


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _141_409 = (new_gamma_cache ())
in (let _141_408 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _141_409; modules = []; expected_typ = None; sigtab = _141_408; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _52_174 = (let _141_463 = (let _141_462 = (FStar_ST.read stack)
in (env)::_141_462)
in (FStar_ST.op_Colon_Equals stack _141_463))
in (

let _52_176 = env
in (let _141_465 = (FStar_Util.smap_copy (gamma_cache env))
in (let _141_464 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_176.solver; range = _52_176.range; curmodule = _52_176.curmodule; gamma = _52_176.gamma; gamma_cache = _141_465; modules = _52_176.modules; expected_typ = _52_176.expected_typ; sigtab = _141_464; is_pattern = _52_176.is_pattern; instantiate_imp = _52_176.instantiate_imp; effects = _52_176.effects; generalize = _52_176.generalize; letrecs = _52_176.letrecs; top_level = _52_176.top_level; check_uvars = _52_176.check_uvars; use_eq = _52_176.use_eq; is_iface = _52_176.is_iface; admit = _52_176.admit; type_of = _52_176.type_of; universe_of = _52_176.universe_of; use_bv_sorts = _52_176.use_bv_sorts})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| env::tl -> begin
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

let _52_191 = (let _141_472 = (pop env)
in (Prims.ignore _141_472))
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


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _141_520 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _141_520)))


let new_u_univ = (fun _52_232 -> (let _141_522 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_141_522)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _52_245) -> begin
(

let _52_247 = ()
in (

let _52_251 = (FStar_Syntax_Subst.open_univ_vars formals t)
in (match (_52_251) with
| (names, t) -> begin
(

let subst = (FStar_List.map2 (fun n u -> FStar_Syntax_Syntax.UName2Univ ((n, u))) names us)
in (let _141_529 = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Instantiation (subst)) t)
in (us, _141_529)))
end)))
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
(let _141_545 = (let _141_544 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _141_543 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _141_542 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _141_541 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _141_544 _141_543 _141_542 _141_541)))))
in (FStar_All.failwith _141_545))
end else begin
()
end
in (let _141_546 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _141_546))))
end
| _52_276 -> begin
(let _141_548 = (let _141_547 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _141_547))
in (FStar_All.failwith _141_548))
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
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
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
(let _141_568 = (let _141_567 = (inst_tscheme t)
in FStar_Util.Inl (_141_567))
in Some (_141_568))
end else begin
None
end
end
| Binding_sig (_52_316, FStar_Syntax_Syntax.Sig_bundle (ses, _52_319, _52_321, _52_323)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _141_570 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _141_570 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
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
| FStar_Syntax_Syntax.Sig_let ((_52_392, lb::[]), _52_397, _52_399, _52_401) -> begin
(let _141_603 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_141_603))
end
| FStar_Syntax_Syntax.Sig_let ((_52_405, lbs), _52_409, _52_411, _52_413) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_418) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _141_605 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_141_605))
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
(let _141_613 = (let _141_612 = (let _141_611 = (variable_not_found bv)
in (let _141_610 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_141_611, _141_610)))
in FStar_Syntax_Syntax.Error (_141_612))
in (Prims.raise _141_613))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_432) -> begin
(let _141_619 = (let _141_618 = (let _141_617 = (let _141_616 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _141_616))
in (ne.FStar_Syntax_Syntax.univs, _141_617))
in (inst_tscheme _141_618))
in Some (_141_619))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_439, _52_441, _52_443) -> begin
(let _141_623 = (let _141_622 = (let _141_621 = (let _141_620 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _141_620))
in (us, _141_621))
in (inst_tscheme _141_622))
in Some (_141_623))
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
(let _141_634 = (inst_tscheme (uvs, t))
in Some (_141_634))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_492), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _141_635 = (inst_tscheme (uvs, t))
in Some (_141_635))
end else begin
None
end
end else begin
(let _141_636 = (inst_tscheme (uvs, t))
in Some (_141_636))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_503, _52_505, _52_507, _52_509), None) -> begin
(match (tps) with
| [] -> begin
(let _141_638 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _141_637 -> Some (_141_637)) _141_638))
end
| _52_517 -> begin
(let _141_643 = (let _141_642 = (let _141_641 = (let _141_640 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _141_640))
in (uvs, _141_641))
in (inst_tscheme _141_642))
in (FStar_All.pipe_left (fun _141_639 -> Some (_141_639)) _141_643))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_523, _52_525, _52_527, _52_529), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _141_645 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _141_644 -> Some (_141_644)) _141_645))
end
| _52_538 -> begin
(let _141_650 = (let _141_649 = (let _141_648 = (let _141_647 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _141_647))
in (uvs, _141_648))
in (inst_tscheme_with _141_649 us))
in (FStar_All.pipe_left (fun _141_646 -> Some (_141_646)) _141_650))
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
in (match ((let _141_651 = (lookup_qname env lid)
in (FStar_Util.bind_opt _141_651 mapper))) with
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
in (match ((let _141_658 = (lookup_qname env lid)
in (FStar_Util.bind_opt _141_658 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _141_665 = (let _141_664 = (let _141_663 = (name_not_found l)
in (_141_663, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_141_664))
in (Prims.raise _141_665))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_595, uvs, t, _52_599, _52_601), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_609 -> begin
(let _141_672 = (let _141_671 = (let _141_670 = (name_not_found lid)
in (_141_670, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_141_671))
in (Prims.raise _141_672))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_613, uvs, t, _52_617, _52_619, _52_621, _52_623, _52_625), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_633 -> begin
(let _141_679 = (let _141_678 = (let _141_677 = (name_not_found lid)
in (_141_677, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_141_678))
in (Prims.raise _141_679))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_643, lbs), _52_647, _52_649, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _141_688 = (let _141_687 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _141_687))
in Some (_141_688))
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
(let _141_695 = (let _141_694 = (let _141_693 = (name_not_found ftv)
in (_141_693, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_141_694))
in (Prims.raise _141_695))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _52_668 -> (match (()) with
| () -> begin
(let _141_706 = (let _141_705 = (FStar_Util.string_of_int i)
in (let _141_704 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _141_705 _141_704)))
in (FStar_All.failwith _141_706))
end))
in (

let _52_672 = (lookup_datacon env lid)
in (match (_52_672) with
| (_52_670, t) -> begin
(match ((let _141_707 = (FStar_Syntax_Subst.compress t)
in _141_707.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_675) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _141_708 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _141_708 Prims.fst)))
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
| (_52_724, _52_731::_52_728::_52_726) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _141_722 = (let _141_721 = (FStar_Syntax_Print.lid_to_string lid)
in (let _141_720 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _141_721 _141_720)))
in (FStar_All.failwith _141_722))
end
| _52_735 -> begin
(

let _52_739 = (let _141_724 = (let _141_723 = (FStar_Syntax_Util.arrow binders c)
in (univs, _141_723))
in (inst_tscheme_with _141_724 insts))
in (match (_52_739) with
| (_52_737, t) -> begin
(match ((let _141_725 = (FStar_Syntax_Subst.compress t)
in _141_725.FStar_Syntax_Syntax.n)) with
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
(let _141_741 = (let _141_740 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _141_740))
in (FStar_All.failwith _141_741))
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


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _141_760 = (FStar_Syntax_Util.un_uinst head)
in _141_760.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_917 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _141_772 = (let _141_771 = (let _141_770 = (name_not_found l)
in (_141_770, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_141_771))
in (Prims.raise _141_772))
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
(let _141_848 = (let _141_847 = (let _141_846 = (let _141_845 = (FStar_Syntax_Print.lid_to_string l1)
in (let _141_844 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _141_845 _141_844)))
in (_141_846, env.range))
in FStar_Syntax_Syntax.Error (_141_847))
in (Prims.raise _141_848))
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
(let _141_863 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _141_863))
end
| Some (md) -> begin
(

let _52_971 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_52_971) with
| (_52_969, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _52_984)::(wp, _52_980)::(wlp, _52_976)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _52_992 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_999) -> begin
(

let effects = (

let _52_1002 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1002.order; joins = _52_1002.joins})
in (

let _52_1005 = env
in {solver = _52_1005.solver; range = _52_1005.range; curmodule = _52_1005.curmodule; gamma = _52_1005.gamma; gamma_cache = _52_1005.gamma_cache; modules = _52_1005.modules; expected_typ = _52_1005.expected_typ; sigtab = _52_1005.sigtab; is_pattern = _52_1005.is_pattern; instantiate_imp = _52_1005.instantiate_imp; effects = effects; generalize = _52_1005.generalize; letrecs = _52_1005.letrecs; top_level = _52_1005.top_level; check_uvars = _52_1005.check_uvars; use_eq = _52_1005.use_eq; is_iface = _52_1005.is_iface; admit = _52_1005.admit; type_of = _52_1005.type_of; universe_of = _52_1005.universe_of; use_bv_sorts = _52_1005.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1009) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _141_878 = (e1.mlift r wp1)
in (e2.mlift r _141_878)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _52_1024 = (inst_tscheme lift_t)
in (match (_52_1024) with
| (_52_1022, lift_t) -> begin
(let _141_890 = (let _141_889 = (let _141_888 = (let _141_887 = (FStar_Syntax_Syntax.as_arg r)
in (let _141_886 = (let _141_885 = (FStar_Syntax_Syntax.as_arg wp1)
in (_141_885)::[])
in (_141_887)::_141_886))
in (lift_t, _141_888))
in FStar_Syntax_Syntax.Tm_app (_141_889))
in (FStar_Syntax_Syntax.mk _141_890 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _141_907 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _141_907 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _141_908 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _141_908 FStar_Syntax_Syntax.Delta_constant None))
in (let _141_909 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _141_909)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _52_1041 -> (match (_52_1041) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _141_915 -> Some (_141_915)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _141_923 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _141_922 = (find_edge order (i, k))
in (let _141_921 = (find_edge order (k, j))
in (_141_922, _141_921)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1053 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _141_923))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _141_1015 = (find_edge order (i, k))
in (let _141_1014 = (find_edge order (j, k))
in (_141_1015, _141_1014)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _52_1070, _52_1072) -> begin
if ((let _141_1016 = (find_edge order (k, ub))
in (FStar_Util.is_some _141_1016)) && (not ((let _141_1017 = (find_edge order (ub, k))
in (FStar_Util.is_some _141_1017))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _52_1076 -> begin
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

let _52_1085 = env.effects
in {decls = _52_1085.decls; order = order; joins = joins})
in (

let _52_1088 = env
in {solver = _52_1088.solver; range = _52_1088.range; curmodule = _52_1088.curmodule; gamma = _52_1088.gamma; gamma_cache = _52_1088.gamma_cache; modules = _52_1088.modules; expected_typ = _52_1088.expected_typ; sigtab = _52_1088.sigtab; is_pattern = _52_1088.is_pattern; instantiate_imp = _52_1088.instantiate_imp; effects = effects; generalize = _52_1088.generalize; letrecs = _52_1088.letrecs; top_level = _52_1088.top_level; check_uvars = _52_1088.check_uvars; use_eq = _52_1088.use_eq; is_iface = _52_1088.is_iface; admit = _52_1088.admit; type_of = _52_1088.type_of; universe_of = _52_1088.universe_of; use_bv_sorts = _52_1088.use_bv_sorts})))))))))))))
end
| _52_1091 -> begin
env
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _141_1066 = (

let _52_1094 = env
in (let _141_1065 = (let _141_1064 = (let _141_1063 = (let _141_1062 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_141_1062, s))
in Binding_sig (_141_1063))
in (_141_1064)::env.gamma)
in {solver = _52_1094.solver; range = _52_1094.range; curmodule = _52_1094.curmodule; gamma = _141_1065; gamma_cache = _52_1094.gamma_cache; modules = _52_1094.modules; expected_typ = _52_1094.expected_typ; sigtab = _52_1094.sigtab; is_pattern = _52_1094.is_pattern; instantiate_imp = _52_1094.instantiate_imp; effects = _52_1094.effects; generalize = _52_1094.generalize; letrecs = _52_1094.letrecs; top_level = _52_1094.top_level; check_uvars = _52_1094.check_uvars; use_eq = _52_1094.use_eq; is_iface = _52_1094.is_iface; admit = _52_1094.admit; type_of = _52_1094.type_of; universe_of = _52_1094.universe_of; use_bv_sorts = _52_1094.use_bv_sorts}))
in (build_lattice _141_1066 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _141_1077 = (

let _52_1099 = env
in (let _141_1076 = (let _141_1075 = (let _141_1074 = (let _141_1073 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_141_1073, s, us))
in Binding_sig_inst (_141_1074))
in (_141_1075)::env.gamma)
in {solver = _52_1099.solver; range = _52_1099.range; curmodule = _52_1099.curmodule; gamma = _141_1076; gamma_cache = _52_1099.gamma_cache; modules = _52_1099.modules; expected_typ = _52_1099.expected_typ; sigtab = _52_1099.sigtab; is_pattern = _52_1099.is_pattern; instantiate_imp = _52_1099.instantiate_imp; effects = _52_1099.effects; generalize = _52_1099.generalize; letrecs = _52_1099.letrecs; top_level = _52_1099.top_level; check_uvars = _52_1099.check_uvars; use_eq = _52_1099.use_eq; is_iface = _52_1099.is_iface; admit = _52_1099.admit; type_of = _52_1099.type_of; universe_of = _52_1099.universe_of; use_bv_sorts = _52_1099.use_bv_sorts}))
in (build_lattice _141_1077 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _52_1103 = env
in {solver = _52_1103.solver; range = _52_1103.range; curmodule = _52_1103.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1103.gamma_cache; modules = _52_1103.modules; expected_typ = _52_1103.expected_typ; sigtab = _52_1103.sigtab; is_pattern = _52_1103.is_pattern; instantiate_imp = _52_1103.instantiate_imp; effects = _52_1103.effects; generalize = _52_1103.generalize; letrecs = _52_1103.letrecs; top_level = _52_1103.top_level; check_uvars = _52_1103.check_uvars; use_eq = _52_1103.use_eq; is_iface = _52_1103.is_iface; admit = _52_1103.admit; type_of = _52_1103.type_of; universe_of = _52_1103.universe_of; use_bv_sorts = _52_1103.use_bv_sorts}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1113 -> (match (_52_1113) with
| (x, _52_1112) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _52_1118 = ()
in (

let x = (

let _52_1120 = x
in {FStar_Syntax_Syntax.ppname = _52_1120.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1120.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _52_1130 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _52_1132 = env
in {solver = _52_1132.solver; range = _52_1132.range; curmodule = _52_1132.curmodule; gamma = []; gamma_cache = _52_1132.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1132.sigtab; is_pattern = _52_1132.is_pattern; instantiate_imp = _52_1132.instantiate_imp; effects = _52_1132.effects; generalize = _52_1132.generalize; letrecs = _52_1132.letrecs; top_level = _52_1132.top_level; check_uvars = _52_1132.check_uvars; use_eq = _52_1132.use_eq; is_iface = _52_1132.is_iface; admit = _52_1132.admit; type_of = _52_1132.type_of; universe_of = _52_1132.universe_of; use_bv_sorts = _52_1132.use_bv_sorts})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _52_1140 = env
in {solver = _52_1140.solver; range = _52_1140.range; curmodule = _52_1140.curmodule; gamma = _52_1140.gamma; gamma_cache = _52_1140.gamma_cache; modules = _52_1140.modules; expected_typ = Some (t); sigtab = _52_1140.sigtab; is_pattern = _52_1140.is_pattern; instantiate_imp = _52_1140.instantiate_imp; effects = _52_1140.effects; generalize = _52_1140.generalize; letrecs = _52_1140.letrecs; top_level = _52_1140.top_level; check_uvars = _52_1140.check_uvars; use_eq = false; is_iface = _52_1140.is_iface; admit = _52_1140.admit; type_of = _52_1140.type_of; universe_of = _52_1140.universe_of; use_bv_sorts = _52_1140.use_bv_sorts}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _141_1120 = (expected_typ env)
in ((

let _52_1147 = env
in {solver = _52_1147.solver; range = _52_1147.range; curmodule = _52_1147.curmodule; gamma = _52_1147.gamma; gamma_cache = _52_1147.gamma_cache; modules = _52_1147.modules; expected_typ = None; sigtab = _52_1147.sigtab; is_pattern = _52_1147.is_pattern; instantiate_imp = _52_1147.instantiate_imp; effects = _52_1147.effects; generalize = _52_1147.generalize; letrecs = _52_1147.letrecs; top_level = _52_1147.top_level; check_uvars = _52_1147.check_uvars; use_eq = false; is_iface = _52_1147.is_iface; admit = _52_1147.admit; type_of = _52_1147.type_of; universe_of = _52_1147.universe_of; use_bv_sorts = _52_1147.use_bv_sorts}), _141_1120)))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _141_1126 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1154, se) -> begin
(se)::[]
end
| _52_1159 -> begin
[]
end))))
in (FStar_All.pipe_right _141_1126 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _52_1161 = (add_sigelts env sigs)
in (

let _52_1163 = env
in {solver = _52_1163.solver; range = _52_1163.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1163.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1163.expected_typ; sigtab = _52_1163.sigtab; is_pattern = _52_1163.is_pattern; instantiate_imp = _52_1163.instantiate_imp; effects = _52_1163.effects; generalize = _52_1163.generalize; letrecs = _52_1163.letrecs; top_level = _52_1163.top_level; check_uvars = _52_1163.check_uvars; use_eq = _52_1163.use_eq; is_iface = _52_1163.is_iface; admit = _52_1163.admit; type_of = _52_1163.type_of; universe_of = _52_1163.universe_of; use_bv_sorts = _52_1163.use_bv_sorts})))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_52_1176)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _141_1138 = (let _141_1137 = (FStar_Syntax_Free.uvars t)
in (ext out _141_1137))
in (aux _141_1138 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
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
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _141_1150 = (let _141_1149 = (FStar_Syntax_Free.univs t)
in (ext out _141_1149))
in (aux _141_1150 tl))
end
| Binding_sig (_52_1246)::_52_1244 -> begin
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


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _141_1157 = (let _141_1156 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _141_1156 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _141_1157 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1278) -> begin
(FStar_List.append lids keys)
end
| _52_1282 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1284 v keys -> (let _141_1180 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _141_1180 keys))) keys)))


let dummy_solver : solver_t = {init = (fun _52_1288 -> ()); push = (fun _52_1290 -> ()); pop = (fun _52_1292 -> ()); mark = (fun _52_1294 -> ()); reset_mark = (fun _52_1296 -> ()); commit_mark = (fun _52_1298 -> ()); encode_modul = (fun _52_1300 _52_1302 -> ()); encode_sig = (fun _52_1304 _52_1306 -> ()); solve = (fun _52_1308 _52_1310 _52_1312 -> ()); is_trivial = (fun _52_1314 _52_1316 -> false); finish = (fun _52_1318 -> ()); refresh = (fun _52_1319 -> ())}


let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _141_1216 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _141_1216)))




