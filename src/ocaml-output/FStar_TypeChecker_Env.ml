
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
| Binding_var (_79_15) -> begin
_79_15
end))

let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_79_18) -> begin
_79_18
end))

let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_79_21) -> begin
_79_21
end))

let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_79_24) -> begin
_79_24
end))

let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_79_27) -> begin
_79_27
end))

type delta_level =
| NoDelta
| OnlyInline
| Unfold

let is_NoDelta = (fun _discr_ -> (match (_discr_) with
| NoDelta -> begin
true
end
| _ -> begin
false
end))

let is_OnlyInline = (fun _discr_ -> (match (_discr_) with
| OnlyInline -> begin
true
end
| _ -> begin
false
end))

let is_Unfold = (fun _discr_ -> (match (_discr_) with
| Unfold -> begin
true
end
| _ -> begin
false
end))

let visible_at = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _79_44 -> begin
false
end))

let glb_delta = (fun d1 d2 -> (match ((d1, d2)) with
| ((NoDelta, _)) | ((_, NoDelta)) -> begin
NoDelta
end
| ((OnlyInline, _)) | ((_, OnlyInline)) -> begin
OnlyInline
end
| (Unfold, Unfold) -> begin
Unfold
end))

type mlift =
FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ}

let is_Mkedge = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))

type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}

let is_Mkeffects = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))

type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap Prims.list; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t); use_bv_sorts : Prims.bool} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}

let is_Mkenv = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let is_Mksolver_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))

let is_Mkguard_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))

type env_t =
env

type implicits =
(env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list

type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap

let default_table_size = 200

let new_sigtab = (fun _79_114 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

let initial_env = (fun tc solver module_lid -> (let _170_359 = (FStar_Util.smap_create 100)
in (let _170_358 = (let _170_357 = (new_sigtab ())
in (_170_357)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _170_359; modules = []; expected_typ = None; sigtab = _170_358; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; use_bv_sorts = false})))

let sigtab = (fun env -> (FStar_List.hd env.sigtab))

let push = (fun env msg -> (let _79_121 = (env.solver.push msg)
in (let _79_123 = env
in (let _170_368 = (let _170_367 = (let _170_366 = (sigtab env)
in (FStar_Util.smap_copy _170_366))
in (_170_367)::env.sigtab)
in {solver = _79_123.solver; range = _79_123.range; curmodule = _79_123.curmodule; gamma = _79_123.gamma; gamma_cache = _79_123.gamma_cache; modules = _79_123.modules; expected_typ = _79_123.expected_typ; sigtab = _170_368; is_pattern = _79_123.is_pattern; instantiate_imp = _79_123.instantiate_imp; effects = _79_123.effects; generalize = _79_123.generalize; letrecs = _79_123.letrecs; top_level = _79_123.top_level; check_uvars = _79_123.check_uvars; use_eq = _79_123.use_eq; is_iface = _79_123.is_iface; admit = _79_123.admit; default_effects = _79_123.default_effects; type_of = _79_123.type_of; use_bv_sorts = _79_123.use_bv_sorts}))))

let mark = (fun env -> (let _79_126 = (env.solver.mark "USER MARK")
in (let _79_128 = env
in (let _170_373 = (let _170_372 = (let _170_371 = (sigtab env)
in (FStar_Util.smap_copy _170_371))
in (_170_372)::env.sigtab)
in {solver = _79_128.solver; range = _79_128.range; curmodule = _79_128.curmodule; gamma = _79_128.gamma; gamma_cache = _79_128.gamma_cache; modules = _79_128.modules; expected_typ = _79_128.expected_typ; sigtab = _170_373; is_pattern = _79_128.is_pattern; instantiate_imp = _79_128.instantiate_imp; effects = _79_128.effects; generalize = _79_128.generalize; letrecs = _79_128.letrecs; top_level = _79_128.top_level; check_uvars = _79_128.check_uvars; use_eq = _79_128.use_eq; is_iface = _79_128.is_iface; admit = _79_128.admit; default_effects = _79_128.default_effects; type_of = _79_128.type_of; use_bv_sorts = _79_128.use_bv_sorts}))))

let commit_mark = (fun env -> (let _79_131 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_79_135::tl -> begin
(hd)::tl
end
| _79_140 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _79_142 = env
in {solver = _79_142.solver; range = _79_142.range; curmodule = _79_142.curmodule; gamma = _79_142.gamma; gamma_cache = _79_142.gamma_cache; modules = _79_142.modules; expected_typ = _79_142.expected_typ; sigtab = sigtab; is_pattern = _79_142.is_pattern; instantiate_imp = _79_142.instantiate_imp; effects = _79_142.effects; generalize = _79_142.generalize; letrecs = _79_142.letrecs; top_level = _79_142.top_level; check_uvars = _79_142.check_uvars; use_eq = _79_142.use_eq; is_iface = _79_142.is_iface; admit = _79_142.admit; default_effects = _79_142.default_effects; type_of = _79_142.type_of; use_bv_sorts = _79_142.use_bv_sorts}))))

let reset_mark = (fun env -> (let _79_145 = (env.solver.reset_mark "USER MARK")
in (let _79_147 = env
in (let _170_378 = (FStar_List.tl env.sigtab)
in {solver = _79_147.solver; range = _79_147.range; curmodule = _79_147.curmodule; gamma = _79_147.gamma; gamma_cache = _79_147.gamma_cache; modules = _79_147.modules; expected_typ = _79_147.expected_typ; sigtab = _170_378; is_pattern = _79_147.is_pattern; instantiate_imp = _79_147.instantiate_imp; effects = _79_147.effects; generalize = _79_147.generalize; letrecs = _79_147.letrecs; top_level = _79_147.top_level; check_uvars = _79_147.check_uvars; use_eq = _79_147.use_eq; is_iface = _79_147.is_iface; admit = _79_147.admit; default_effects = _79_147.default_effects; type_of = _79_147.type_of; use_bv_sorts = _79_147.use_bv_sorts}))))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _79_157::tl -> begin
(let _79_159 = (env.solver.pop msg)
in (let _79_161 = env
in {solver = _79_161.solver; range = _79_161.range; curmodule = _79_161.curmodule; gamma = _79_161.gamma; gamma_cache = _79_161.gamma_cache; modules = _79_161.modules; expected_typ = _79_161.expected_typ; sigtab = tl; is_pattern = _79_161.is_pattern; instantiate_imp = _79_161.instantiate_imp; effects = _79_161.effects; generalize = _79_161.generalize; letrecs = _79_161.letrecs; top_level = _79_161.top_level; check_uvars = _79_161.check_uvars; use_eq = _79_161.use_eq; is_iface = _79_161.is_iface; admit = _79_161.admit; default_effects = _79_161.default_effects; type_of = _79_161.type_of; use_bv_sorts = _79_161.use_bv_sorts}))
end))

let debug = (fun env l -> ((let _170_388 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _170_388 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

let set_range = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(let _79_168 = e
in {solver = _79_168.solver; range = r; curmodule = _79_168.curmodule; gamma = _79_168.gamma; gamma_cache = _79_168.gamma_cache; modules = _79_168.modules; expected_typ = _79_168.expected_typ; sigtab = _79_168.sigtab; is_pattern = _79_168.is_pattern; instantiate_imp = _79_168.instantiate_imp; effects = _79_168.effects; generalize = _79_168.generalize; letrecs = _79_168.letrecs; top_level = _79_168.top_level; check_uvars = _79_168.check_uvars; use_eq = _79_168.use_eq; is_iface = _79_168.is_iface; admit = _79_168.admit; default_effects = _79_168.default_effects; type_of = _79_168.type_of; use_bv_sorts = _79_168.use_bv_sorts})
end)

let get_range = (fun e -> e.range)

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _79_175 = env
in {solver = _79_175.solver; range = _79_175.range; curmodule = lid; gamma = _79_175.gamma; gamma_cache = _79_175.gamma_cache; modules = _79_175.modules; expected_typ = _79_175.expected_typ; sigtab = _79_175.sigtab; is_pattern = _79_175.is_pattern; instantiate_imp = _79_175.instantiate_imp; effects = _79_175.effects; generalize = _79_175.generalize; letrecs = _79_175.letrecs; top_level = _79_175.top_level; check_uvars = _79_175.check_uvars; use_eq = _79_175.use_eq; is_iface = _79_175.is_iface; admit = _79_175.admit; default_effects = _79_175.default_effects; type_of = _79_175.type_of; use_bv_sorts = _79_175.use_bv_sorts}))

let has_interface = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

let find_in_sigtab = (fun env lid -> (let _170_412 = (sigtab env)
in (FStar_Util.smap_try_find _170_412 (FStar_Ident.text_of_lid lid))))

let name_not_found = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

let variable_not_found = (fun v -> (let _170_417 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _170_417)))

let new_u_univ = (fun _79_184 -> (let _170_419 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_170_419)))

let inst_tscheme_with = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _79_197) -> begin
(let _79_199 = ()
in (let n = ((FStar_List.length formals) - 1)
in (let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _170_426 = (FStar_Syntax_Subst.subst vs t)
in (us, _170_426)))))
end))

let inst_tscheme = (fun _79_1 -> (match (_79_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(let us' = (FStar_All.pipe_right us (FStar_List.map (fun _79_212 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

let inst_effect_fun = (fun env ed _79_219 -> (match (_79_219) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(let _170_436 = (inst_tscheme ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t))
in (Prims.snd _170_436))
end
| _79_222 -> begin
(let _170_438 = (let _170_437 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _170_437))
in (FStar_All.failwith _170_438))
end)
end))

type tri =
| Yes
| No
| Maybe

let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes -> begin
true
end
| _ -> begin
false
end))

let is_No = (fun _discr_ -> (match (_discr_) with
| No -> begin
true
end
| _ -> begin
false
end))

let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe -> begin
true
end
| _ -> begin
false
end))

let in_cur_mod = (fun env l -> (let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (let rec aux = (fun c l -> (match ((c, l)) with
| ([], _79_233) -> begin
Maybe
end
| (_79_236, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _79_247 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

let lookup_qname = (fun env lid -> (let cur_mod = (in_cur_mod env lid)
in (let cache = (fun t -> (let _79_253 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _79_2 -> (match (_79_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _170_458 = (let _170_457 = (inst_tscheme t)
in FStar_Util.Inl (_170_457))
in Some (_170_458))
end else begin
None
end
end
| Binding_sig (_79_262, FStar_Syntax_Syntax.Sig_bundle (ses, _79_265, _79_267, _79_269)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _170_460 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _170_460 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_79_282) -> begin
Some (t)
end
| _79_285 -> begin
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
| _79_292 -> begin
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

let rec add_sigelt = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _79_302, _79_304, _79_306) -> begin
(add_sigelts env ses)
end
| _79_310 -> begin
(let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _170_470 = (sigtab env)
in (FStar_Util.smap_add _170_470 l.FStar_Ident.str se))) lids))
end))
and add_sigelts = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

let try_lookup_bv = (fun env bv -> (FStar_Util.find_map env.gamma (fun _79_3 -> (match (_79_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _79_321 -> begin
None
end))))

let lookup_univ = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _79_4 -> (match (_79_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _79_328 -> begin
false
end)) env.gamma) FStar_Option.isSome))

let lookup_type_of_let = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_79_332, lb::[]), _79_337, _79_339, _79_341) -> begin
(let _170_490 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_170_490))
end
| FStar_Syntax_Syntax.Sig_let ((_79_345, lbs), _79_349, _79_351, _79_353) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_79_358) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Ident.lid_equals lid lid') then begin
(let _170_492 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_170_492))
end else begin
None
end
end)))
end
| _79_363 -> begin
None
end))

let lookup_bv = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _170_500 = (let _170_499 = (let _170_498 = (variable_not_found bv)
in (let _170_497 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_170_498, _170_497)))
in FStar_Syntax_Syntax.Error (_170_499))
in (Prims.raise _170_500))
end
| Some (t) -> begin
t
end))

let effect_signature = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _79_372) -> begin
(let _170_506 = (let _170_505 = (let _170_504 = (let _170_503 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _170_503))
in (ne.FStar_Syntax_Syntax.univs, _170_504))
in (inst_tscheme _170_505))
in Some (_170_506))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _79_379, _79_381, _79_383) -> begin
(let _170_510 = (let _170_509 = (let _170_508 = (let _170_507 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _170_507))
in (us, _170_508))
in (inst_tscheme _170_509))
in Some (_170_510))
end
| _79_387 -> begin
None
end))

let try_lookup_effect_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_79_397, t) -> begin
Some (t)
end)
end
| _79_402 -> begin
None
end))

let try_lookup_lid = (fun env lid -> (let mapper = (fun _79_5 -> (match (_79_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (_79_409, uvs, t, _79_413, _79_415, _79_417, _79_419, _79_421)), None) -> begin
(let _170_521 = (inst_tscheme (uvs, t))
in Some (_170_521))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _79_432), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _170_522 = (inst_tscheme (uvs, t))
in Some (_170_522))
end else begin
None
end
end else begin
(let _170_523 = (inst_tscheme (uvs, t))
in Some (_170_523))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (lid, uvs, tps, k, _79_443, _79_445, _79_447, _79_449)), None) -> begin
(match (tps) with
| [] -> begin
(let _170_525 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _170_524 -> Some (_170_524)) _170_525))
end
| _79_457 -> begin
(let _170_530 = (let _170_529 = (let _170_528 = (let _170_527 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _170_527))
in (uvs, _170_528))
in (inst_tscheme _170_529))
in (FStar_All.pipe_left (fun _170_526 -> Some (_170_526)) _170_530))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (lid, uvs, tps, k, _79_463, _79_465, _79_467, _79_469)), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _170_532 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _170_531 -> Some (_170_531)) _170_532))
end
| _79_478 -> begin
(let _170_537 = (let _170_536 = (let _170_535 = (let _170_534 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _170_534))
in (uvs, _170_535))
in (inst_tscheme_with _170_536 us))
in (FStar_All.pipe_left (fun _170_533 -> Some (_170_533)) _170_537))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_79_482), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _79_487 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _170_538 = (lookup_qname env lid)
in (FStar_Util.bind_opt _170_538 mapper))) with
| Some (us, t) -> begin
Some ((us, (let _79_493 = t
in {FStar_Syntax_Syntax.n = _79_493.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _79_493.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _79_493.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

let lookup_lid = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _170_545 = (let _170_544 = (let _170_543 = (name_not_found l)
in (_170_543, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_170_544))
in (Prims.raise _170_545))
end
| Some (x) -> begin
x
end))

let lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_79_504, uvs, t, _79_508, _79_510), None)) -> begin
(inst_tscheme (uvs, t))
end
| _79_518 -> begin
(let _170_552 = (let _170_551 = (let _170_550 = (name_not_found lid)
in (_170_550, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_170_551))
in (Prims.raise _170_552))
end))

let lookup_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (_79_522, uvs, t, _79_526, _79_528, _79_530, _79_532, _79_534)), None)) -> begin
(inst_tscheme (uvs, t))
end
| _79_542 -> begin
(let _170_559 = (let _170_558 = (let _170_557 = (name_not_found lid)
in (_170_557, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_170_558))
in (Prims.raise _170_559))
end))

let lookup_definition = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_79_552, lbs), _79_556, _79_558, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (let lid' = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Ident.lid_equals lid lid') then begin
(let _170_568 = (let _170_567 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _170_567))
in Some (_170_568))
end else begin
None
end)))
end
| _79_565 -> begin
None
end)
end
| _79_567 -> begin
None
end))

let lookup_effect_lid = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _170_575 = (let _170_574 = (let _170_573 = (name_not_found ftv)
in (_170_573, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_170_574))
in (Prims.raise _170_575))
end
| Some (k) -> begin
k
end))

let lookup_projector = (fun env lid i -> (let fail = (fun _79_577 -> (match (()) with
| () -> begin
(let _170_586 = (let _170_585 = (FStar_Util.string_of_int i)
in (let _170_584 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _170_585 _170_584)))
in (FStar_All.failwith _170_586))
end))
in (let _79_581 = (lookup_datacon env lid)
in (match (_79_581) with
| (_79_579, t) -> begin
(match ((let _170_587 = (FStar_Syntax_Subst.compress t)
in _170_587.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _79_584) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (let _170_588 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _170_588 Prims.fst)))
end
end
| _79_589 -> begin
(fail ())
end)
end))))

let try_lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_79_593, uvs, t, q, _79_598), None)) -> begin
Some (((uvs, t), q))
end
| _79_606 -> begin
None
end))

let lookup_effect_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _79_615), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_6 -> (match (_79_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _79_625 -> begin
false
end)))) then begin
None
end else begin
(let _79_630 = (FStar_Syntax_Util.open_univ_vars_binders_and_comp univs binders c)
in (match (_79_630) with
| (_79_627, binders, c) -> begin
Some ((binders, c))
end))
end
end
| _79_632 -> begin
None
end))

let datacons_of_typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (_79_636, _79_638, _79_640, _79_642, _79_644, dcs, _79_647, _79_649)), _79_653)) -> begin
dcs
end
| _79_658 -> begin
[]
end))

let typ_of_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (_79_662, _79_664, _79_666, l, _79_669, _79_671, _79_673, _79_675)), _79_679)) -> begin
l
end
| _79_684 -> begin
(let _170_607 = (let _170_606 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _170_606))
in (FStar_All.failwith _170_607))
end))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (_79_688, _79_690, _79_692, _79_694, _79_696, _79_698, _79_700, _79_702)), _79_706)) -> begin
true
end
| _79_711 -> begin
false
end))

let is_record = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (_79_715, _79_717, _79_719, _79_721, _79_723, _79_725, tags, _79_728)), _79_732)) -> begin
(FStar_Util.for_some (fun _79_7 -> (match (_79_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _79_744 -> begin
false
end)) tags)
end
| _79_746 -> begin
false
end))

let is_projector = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_79_750, _79_752, _79_754, quals, _79_757), _79_761)) -> begin
(FStar_Util.for_some (fun _79_8 -> (match (_79_8) with
| FStar_Syntax_Syntax.Projector (_79_767) -> begin
true
end
| _79_770 -> begin
false
end)) quals)
end
| _79_772 -> begin
false
end))

let effect_decl_opt = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

let get_effect_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _170_633 = (let _170_632 = (let _170_631 = (name_not_found l)
in (_170_631, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_170_632))
in (Prims.raise _170_633))
end
| Some (md) -> begin
md
end))

let join = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _79_800 -> (match (_79_800) with
| (m1, m2, _79_795, _79_797, _79_799) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _170_709 = (let _170_708 = (let _170_707 = (let _170_706 = (FStar_Syntax_Print.lid_to_string l1)
in (let _170_705 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _170_706 _170_705)))
in (_170_707, env.range))
in FStar_Syntax_Syntax.Error (_170_708))
in (Prims.raise _170_709))
end
| Some (_79_803, _79_805, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

let monad_leq = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

let wp_sig_aux = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _170_724 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _170_724))
end
| Some (md) -> begin
(let _79_826 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_79_826) with
| (_79_824, s) -> begin
(let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _79_839)::(wp, _79_835)::(wlp, _79_831)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _79_847 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

let wp_signature = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect = (fun env l -> (FStar_Util.find_map env.default_effects (fun _79_854 -> (match (_79_854) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _79_859, _79_861, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _79_9 -> (match (_79_9) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _79_871 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _79_875 = env
in {solver = _79_875.solver; range = _79_875.range; curmodule = _79_875.curmodule; gamma = _79_875.gamma; gamma_cache = _79_875.gamma_cache; modules = _79_875.modules; expected_typ = _79_875.expected_typ; sigtab = _79_875.sigtab; is_pattern = _79_875.is_pattern; instantiate_imp = _79_875.instantiate_imp; effects = _79_875.effects; generalize = _79_875.generalize; letrecs = _79_875.letrecs; top_level = _79_875.top_level; check_uvars = _79_875.check_uvars; use_eq = _79_875.use_eq; is_iface = _79_875.is_iface; admit = _79_875.admit; default_effects = ((e, l))::env.default_effects; type_of = _79_875.type_of; use_bv_sorts = _79_875.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _79_879) -> begin
(let effects = (let _79_882 = env.effects
in {decls = (ne)::env.effects.decls; order = _79_882.order; joins = _79_882.joins})
in (let _79_885 = env
in {solver = _79_885.solver; range = _79_885.range; curmodule = _79_885.curmodule; gamma = _79_885.gamma; gamma_cache = _79_885.gamma_cache; modules = _79_885.modules; expected_typ = _79_885.expected_typ; sigtab = _79_885.sigtab; is_pattern = _79_885.is_pattern; instantiate_imp = _79_885.instantiate_imp; effects = effects; generalize = _79_885.generalize; letrecs = _79_885.letrecs; top_level = _79_885.top_level; check_uvars = _79_885.check_uvars; use_eq = _79_885.use_eq; is_iface = _79_885.is_iface; admit = _79_885.admit; default_effects = _79_885.default_effects; type_of = _79_885.type_of; use_bv_sorts = _79_885.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _79_889) -> begin
(let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _170_745 = (e1.mlift r wp1)
in (e2.mlift r _170_745)))})
in (let mk_lift = (fun lift_t r wp1 -> (let _79_904 = (inst_tscheme lift_t)
in (match (_79_904) with
| (_79_902, lift_t) -> begin
(let _170_757 = (let _170_756 = (let _170_755 = (let _170_754 = (FStar_Syntax_Syntax.as_arg r)
in (let _170_753 = (let _170_752 = (FStar_Syntax_Syntax.as_arg wp1)
in (_170_752)::[])
in (_170_754)::_170_753))
in (lift_t, _170_755))
in FStar_Syntax_Syntax.Tm_app (_170_756))
in (FStar_Syntax_Syntax.mk _170_757 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (let print_mlift = (fun l -> (let arg = (let _170_774 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _170_774 None))
in (let wp = (let _170_775 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _170_775 None))
in (let _170_776 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _170_776)))))
in (let order = (edge)::env.effects.order
in (let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (let find_edge = (fun order _79_921 -> (match (_79_921) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _170_782 -> Some (_170_782)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _170_790 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _170_789 = (find_edge order (i, k))
in (let _170_788 = (find_edge order (k, j))
in (_170_789, _170_788)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _79_933 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _170_790))) order))
in (let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _170_882 = (find_edge order (i, k))
in (let _170_881 = (find_edge order (j, k))
in (_170_882, _170_881)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _79_950, _79_952) -> begin
if ((let _170_883 = (find_edge order (k, ub))
in (FStar_Util.is_some _170_883)) && (not ((let _170_884 = (find_edge order (ub, k))
in (FStar_Util.is_some _170_884))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _79_956 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _79_965 = env.effects
in {decls = _79_965.decls; order = order; joins = joins})
in (let _79_968 = env
in {solver = _79_968.solver; range = _79_968.range; curmodule = _79_968.curmodule; gamma = _79_968.gamma; gamma_cache = _79_968.gamma_cache; modules = _79_968.modules; expected_typ = _79_968.expected_typ; sigtab = _79_968.sigtab; is_pattern = _79_968.is_pattern; instantiate_imp = _79_968.instantiate_imp; effects = effects; generalize = _79_968.generalize; letrecs = _79_968.letrecs; top_level = _79_968.top_level; check_uvars = _79_968.check_uvars; use_eq = _79_968.use_eq; is_iface = _79_968.is_iface; admit = _79_968.admit; default_effects = _79_968.default_effects; type_of = _79_968.type_of; use_bv_sorts = _79_968.use_bv_sorts})))))))))))))
end
| _79_971 -> begin
env
end))

let push_sigelt = (fun env s -> (let _170_933 = (let _79_974 = env
in (let _170_932 = (let _170_931 = (let _170_930 = (let _170_929 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_170_929, s))
in Binding_sig (_170_930))
in (_170_931)::env.gamma)
in {solver = _79_974.solver; range = _79_974.range; curmodule = _79_974.curmodule; gamma = _170_932; gamma_cache = _79_974.gamma_cache; modules = _79_974.modules; expected_typ = _79_974.expected_typ; sigtab = _79_974.sigtab; is_pattern = _79_974.is_pattern; instantiate_imp = _79_974.instantiate_imp; effects = _79_974.effects; generalize = _79_974.generalize; letrecs = _79_974.letrecs; top_level = _79_974.top_level; check_uvars = _79_974.check_uvars; use_eq = _79_974.use_eq; is_iface = _79_974.is_iface; admit = _79_974.admit; default_effects = _79_974.default_effects; type_of = _79_974.type_of; use_bv_sorts = _79_974.use_bv_sorts}))
in (build_lattice _170_933 s)))

let push_sigelt_inst = (fun env s us -> (let _170_944 = (let _79_979 = env
in (let _170_943 = (let _170_942 = (let _170_941 = (let _170_940 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_170_940, s, us))
in Binding_sig_inst (_170_941))
in (_170_942)::env.gamma)
in {solver = _79_979.solver; range = _79_979.range; curmodule = _79_979.curmodule; gamma = _170_943; gamma_cache = _79_979.gamma_cache; modules = _79_979.modules; expected_typ = _79_979.expected_typ; sigtab = _79_979.sigtab; is_pattern = _79_979.is_pattern; instantiate_imp = _79_979.instantiate_imp; effects = _79_979.effects; generalize = _79_979.generalize; letrecs = _79_979.letrecs; top_level = _79_979.top_level; check_uvars = _79_979.check_uvars; use_eq = _79_979.use_eq; is_iface = _79_979.is_iface; admit = _79_979.admit; default_effects = _79_979.default_effects; type_of = _79_979.type_of; use_bv_sorts = _79_979.use_bv_sorts}))
in (build_lattice _170_944 s)))

let push_local_binding = (fun env b -> (let _79_983 = env
in {solver = _79_983.solver; range = _79_983.range; curmodule = _79_983.curmodule; gamma = (b)::env.gamma; gamma_cache = _79_983.gamma_cache; modules = _79_983.modules; expected_typ = _79_983.expected_typ; sigtab = _79_983.sigtab; is_pattern = _79_983.is_pattern; instantiate_imp = _79_983.instantiate_imp; effects = _79_983.effects; generalize = _79_983.generalize; letrecs = _79_983.letrecs; top_level = _79_983.top_level; check_uvars = _79_983.check_uvars; use_eq = _79_983.use_eq; is_iface = _79_983.is_iface; admit = _79_983.admit; default_effects = _79_983.default_effects; type_of = _79_983.type_of; use_bv_sorts = _79_983.use_bv_sorts}))

let push_bv = (fun env x -> (push_local_binding env (Binding_var (x))))

let push_binders = (fun env bs -> (FStar_List.fold_left (fun env _79_993 -> (match (_79_993) with
| (x, _79_992) -> begin
(push_bv env x)
end)) env bs))

let binding_of_lb = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(let _79_998 = ()
in (let x = (let _79_1000 = x
in {FStar_Syntax_Syntax.ppname = _79_1000.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _79_1000.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (lid) -> begin
Binding_lid ((lid, t))
end))

let push_let_binding = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

let push_module = (fun env m -> (let _79_1010 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (let _79_1012 = env
in {solver = _79_1012.solver; range = _79_1012.range; curmodule = _79_1012.curmodule; gamma = []; gamma_cache = _79_1012.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _79_1012.sigtab; is_pattern = _79_1012.is_pattern; instantiate_imp = _79_1012.instantiate_imp; effects = _79_1012.effects; generalize = _79_1012.generalize; letrecs = _79_1012.letrecs; top_level = _79_1012.top_level; check_uvars = _79_1012.check_uvars; use_eq = _79_1012.use_eq; is_iface = _79_1012.is_iface; admit = _79_1012.admit; default_effects = _79_1012.default_effects; type_of = _79_1012.type_of; use_bv_sorts = _79_1012.use_bv_sorts})))

let push_univ_vars = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

let set_expected_typ = (fun env t -> (let _79_1020 = env
in {solver = _79_1020.solver; range = _79_1020.range; curmodule = _79_1020.curmodule; gamma = _79_1020.gamma; gamma_cache = _79_1020.gamma_cache; modules = _79_1020.modules; expected_typ = Some (t); sigtab = _79_1020.sigtab; is_pattern = _79_1020.is_pattern; instantiate_imp = _79_1020.instantiate_imp; effects = _79_1020.effects; generalize = _79_1020.generalize; letrecs = _79_1020.letrecs; top_level = _79_1020.top_level; check_uvars = _79_1020.check_uvars; use_eq = false; is_iface = _79_1020.is_iface; admit = _79_1020.admit; default_effects = _79_1020.default_effects; type_of = _79_1020.type_of; use_bv_sorts = _79_1020.use_bv_sorts}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> (let _170_987 = (expected_typ env)
in ((let _79_1027 = env
in {solver = _79_1027.solver; range = _79_1027.range; curmodule = _79_1027.curmodule; gamma = _79_1027.gamma; gamma_cache = _79_1027.gamma_cache; modules = _79_1027.modules; expected_typ = None; sigtab = _79_1027.sigtab; is_pattern = _79_1027.is_pattern; instantiate_imp = _79_1027.instantiate_imp; effects = _79_1027.effects; generalize = _79_1027.generalize; letrecs = _79_1027.letrecs; top_level = _79_1027.top_level; check_uvars = _79_1027.check_uvars; use_eq = false; is_iface = _79_1027.is_iface; admit = _79_1027.admit; default_effects = _79_1027.default_effects; type_of = _79_1027.type_of; use_bv_sorts = _79_1027.use_bv_sorts}), _170_987)))

let finish_module = (let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _79_10 -> (match (_79_10) with
| Binding_sig (_79_1034, se) -> begin
(se)::[]
end
| _79_1039 -> begin
[]
end))))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (let _79_1041 = (add_sigelts env sigs)
in (let _79_1043 = (FStar_Util.smap_clear env.gamma_cache)
in (let _79_1045 = env
in {solver = _79_1045.solver; range = _79_1045.range; curmodule = empty_lid; gamma = []; gamma_cache = _79_1045.gamma_cache; modules = (m)::env.modules; expected_typ = _79_1045.expected_typ; sigtab = _79_1045.sigtab; is_pattern = _79_1045.is_pattern; instantiate_imp = _79_1045.instantiate_imp; effects = _79_1045.effects; generalize = _79_1045.generalize; letrecs = _79_1045.letrecs; top_level = _79_1045.top_level; check_uvars = _79_1045.check_uvars; use_eq = _79_1045.use_eq; is_iface = _79_1045.is_iface; admit = _79_1045.admit; default_effects = _79_1045.default_effects; type_of = _79_1045.type_of; use_bv_sorts = _79_1045.use_bv_sorts}))))))

let uvars_in_env = (fun env -> (let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_79_1058)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _170_1004 = (let _170_1003 = (FStar_Syntax_Free.uvars t)
in (ext out _170_1003))
in (aux _170_1004 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

let univ_vars = (fun env -> (let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _170_1016 = (let _170_1015 = (FStar_Syntax_Free.univs t)
in (ext out _170_1015))
in (aux _170_1016 tl))
end
| Binding_sig (_79_1128)::_79_1126 -> begin
out
end))
in (aux no_univs env.gamma)))))

let bound_vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _79_11 -> (match (_79_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

let binders_of_bindings = (fun bs -> (let _170_1023 = (let _170_1022 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _170_1022 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _170_1023 FStar_List.rev)))

let bound_vars = (fun env -> (bound_vars_of_bindings env.gamma))

let all_binders = (fun env -> (binders_of_bindings env.gamma))

let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

let lidents = (fun env -> (let keys = (FStar_List.fold_left (fun keys _79_12 -> (match (_79_12) with
| Binding_sig (lids, _79_1160) -> begin
(FStar_List.append lids keys)
end
| _79_1164 -> begin
keys
end)) [] env.gamma)
in (let _170_1047 = (sigtab env)
in (FStar_Util.smap_fold _170_1047 (fun _79_1166 v keys -> (let _170_1046 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _170_1046 keys))) keys))))

let dummy_solver = {init = (fun _79_1170 -> ()); push = (fun _79_1172 -> ()); pop = (fun _79_1174 -> ()); mark = (fun _79_1176 -> ()); reset_mark = (fun _79_1178 -> ()); commit_mark = (fun _79_1180 -> ()); encode_modul = (fun _79_1182 _79_1184 -> ()); encode_sig = (fun _79_1186 _79_1188 -> ()); solve = (fun _79_1190 _79_1192 -> ()); is_trivial = (fun _79_1194 _79_1196 -> false); finish = (fun _79_1198 -> ()); refresh = (fun _79_1199 -> ())}

let no_solver_env = (fun tc -> (let _170_1076 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _170_1076)))




